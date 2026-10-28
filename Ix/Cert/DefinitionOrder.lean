import Ix.Cert.RecordTransfer

/-! # The dependency order of a definition block, as the reader computes it

The reader reads a definition block's members in `Ix.Kernel.Reader.defOrder` over which members
each member's terms name by `recur` (`recurDeps`). This module states what both depend on.

* `defOrder_congr`: `defOrder` reads a member's dependency set only at the other members, so two
  dependency arrays that agree there give the same order.
* `recurDeps_read`: a member names member `j` by `recur`, through the record's sharing table,
  exactly where the member reader, with each member `j` read as a key `K j` that no reference of
  the context reads as, reads a term mentioning `K j` (`Frontend.occursConst`).
* `freshKey`: such keys exist for every context: derived keys deeper than every key its roles
  bind. -/

namespace Ix.Cert.DefinitionOrder

open Ix.Kernel Ix.Kernel.Reader

/-! ## The order -/

/-- **Dependency arrays that agree at the other members give the same order.** -/
theorem defOrder_congr {d₁ d₂ : Array (Std.HashSet Nat)} (hsize : d₁.size = d₂.size)
    (hmem : ∀ i < d₁.size, ∀ j < d₁.size, j ≠ i → (j ∈ d₁[i]! ↔ j ∈ d₂[i]!)) :
    defOrder d₁ = defOrder d₂ := by
  have key : ∀ (i : Nat) (done : Array Bool),
      (d₁[i]!.toList.all fun j => j == i || decide (j ≥ d₁.size) || done[j]!) =
        (d₂[i]!.toList.all fun j => j == i || decide (j ≥ d₂.size) || done[j]!) := by
    intro i done
    rw [← hsize]
    by_cases hi : i < d₁.size
    · rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      have side : ∀ j, (j == i || decide (j ≥ d₁.size) || done[j]!) = true ∨ (j < d₁.size ∧ j ≠ i) := by
        intro j
        by_cases hji : j = i
        · exact .inl (by simp [hji])
        · by_cases hjn : j ≥ d₁.size
          · exact .inl (by simp [hjn])
          · exact .inr ⟨by omega, hji⟩
      constructor
      · intro h j hj
        rcases side j with done' | ⟨hjn, hji⟩
        · exact done'
        · exact h j (Std.HashSet.mem_toList.mpr ((hmem i hi j hjn hji).mpr (Std.HashSet.mem_toList.mp hj)))
      · intro h j hj
        rcases side j with done' | ⟨hjn, hji⟩
        · exact done'
        · exact h j (Std.HashSet.mem_toList.mpr ((hmem i hi j hjn hji).mp (Std.HashSet.mem_toList.mp hj)))
    · rw [getElem!_neg d₁ i hi, getElem!_neg d₂ i (by omega)]
  unfold defOrder
  simp only [key]
  rw [hsize]

/-- A loop in `Id` keeps an invariant its steps keep. -/
theorem forIn_id_inv {α S : Type} (Inv : S → Prop) (f : α → S → Id (ForInStep S)) :
    ∀ (l : List α) (s : S), Inv s → (∀ a ∈ l, ∀ s, Inv s → Inv (f a s).value) → Inv (forIn l s f)
  | [], s, hs, _ => by rw [List.forIn_nil]; exact hs
  | a :: l, s, hs, step => by
    rw [List.forIn_cons]
    have ha := step a List.mem_cons_self s hs
    cases hfa : f a s with
    | done b =>
      rw [hfa] at ha
      exact ha
    | yield b =>
      rw [hfa] at ha
      exact forIn_id_inv Inv f l b ha (fun x hx => step x (List.mem_cons_of_mem _ hx))
/-- **The order lists members only.** -/
theorem defOrder_lt (deps : Array (Std.HashSet Nat)) (out : Array Nat) (h : defOrder deps = some out) :
    ∀ i ∈ out, i < deps.size := by
  unfold defOrder at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have hsize : [:deps.size].size = deps.size := by simp [Std.Legacy.Range.size]
  generalize hS : forIn (m := Id) (List.range' 0 [:deps.size].size) _ _ = S at h
  have inv : (∀ x ∈ S.2.2, x < deps.size) ∧ ∀ o, S.1 = some (some o) → ∀ x ∈ o, x < deps.size := by
    rw [← hS]
    refine forIn_id_inv (fun s : Option (Option (Array Nat)) × Array Bool × Array Nat =>
      (∀ x ∈ s.2.2, x < deps.size) ∧ ∀ o, s.1 = some (some o) → ∀ x ∈ o, x < deps.size) _ _ _
      ⟨by simp, by simp⟩ ?_
    intro a _ s hs
    generalize hT : forIn (m := Id) (List.range' 0 [:deps.size].size) (s.2.1, s.2.2, false) _ = T
    have tinv : ∀ x ∈ T.2.1, x < deps.size := by
      rw [← hT]
      refine forIn_id_inv (fun t : Array Bool × Array Nat × Bool => ∀ x ∈ t.2.1, x < deps.size) _ _ _ hs.1 ?_
      intro i hi t ht
      rw [List.mem_range', hsize] at hi
      split
      · intro x hx
        rcases Array.mem_push.mp hx with hx | rfl
        · exact ht x hx
        · omega
      · exact ht
    rw [show ∀ {β γ : Type} (x : Id β) (g : β → Id γ), x >>= g = g x from fun _ _ => rfl]
    split
    · refine ⟨tinv, fun o ho => ?_⟩
      have ho' : some (some T.2.1) = some (some o) := ho
      cases ho'
      exact tinv
    · split
      · exact ⟨tinv, fun o ho => by cases ho⟩
      · exact ⟨tinv, fun o ho => by cases ho⟩
  obtain ⟨r, dn, o⟩ := S
  cases r with
  | some r =>
    cases r with
    | some o' =>
      have := inv.2 o' rfl
      have h' : some o' = some out := h
      cases h'
      exact this
    | none =>
      have h' : (none : Option (Array Nat)) = some out := h
      cases h'
  | none =>
    have h' : (if (o.size == deps.size) = true then some o else none) = some out := h
    clear h
    split at h'
    · cases h'
      exact inv.1
    · cases h'

/-! ## `recur` references -/

theorem mem_foldl_insert : ∀ (l : List Nat) (acc : Std.HashSet Nat) (j : Nat),
    j ∈ l.foldl (fun a x => a.insert x) acc ↔ j ∈ acc ∨ j ∈ l
  | [], acc, j => by simp
  | x :: l, acc, j => by
    rw [List.foldl_cons, mem_foldl_insert l _ j, Std.HashSet.mem_insert, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact .inr (.inl (beq_iff_eq.mp h).symm)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl (beq_iff_eq.mpr h.symm))
      · exact .inr h

theorem mem_fold_insert (s acc : Std.HashSet Nat) (j : Nat) :
    j ∈ s.fold (fun a x => a.insert x) acc ↔ j ∈ acc ∨ j ∈ s := by
  rw [Std.HashSet.fold_eq_foldl_toList, mem_foldl_insert, Std.HashSet.mem_toList]

/-- The self references of a block of `N` members, member `k` read as the key `K k`. -/
def tagSelf {md : Mode} (N : Nat) (K : Nat → CName md) : Nat → Option (ReadM (CName md)) :=
  fun k => if k < N then some (pure (K k)) else none

/-- The dependency table `recurDeps` builds, as a fold. -/
def sharedFold (l : List Ixon.Expr) (shared : Array (Std.HashSet Nat)) : Array (Std.HashSet Nat) :=
  l.foldl (fun s entry => s.push (recurDeps.go s {} entry)) shared

theorem recurDeps_eq (c : Ixon.Constant) (d : Ixon.Definition) :
    recurDeps c d = recurDeps.go (sharedFold c.sharing.toList #[])
      (recurDeps.go (sharedFold c.sharing.toList #[]) {} d.typ) d.value := by
  simp only [recurDeps, Id.run, sharedFold, Array.forIn_pure_yield_eq_foldl, ← Array.foldl_toList]
  rfl

section Tagged

variable {md : Mode} (cx : Ctx md) (c : Ixon.Constant) (univs : Array CLevel) (N : Nat)
  (K : Nat → CName md)

/-- A dependency table and a reading table agree: each entry the reader reads, the dependency
table holds the members its reading mentions. -/
def Agree (shared : Array (Std.HashSet Nat)) (tbl : Array (ReadM (CExpr md))) : Prop :=
  shared.size = tbl.size ∧ ∀ (i : Nat) (t : CExpr md), tbl[i]? = some (.ok t) →
    ∀ j, j ∈ shared[i]! ↔ Frontend.occursConst (K j) t = true

variable {cx c univs N K}

theorem go_read (inj : ∀ a b, K a = K b → a = b)
    (fresh : ∀ a k, cx.keyAt a = .ok k → ∀ j, k ≠ K j)
    {shared : Array (Std.HashSet Nat)} {tbl : Array (ReadM (CExpr md))} (agree : Agree K shared tbl) :
    ∀ (e : Ixon.Expr) (t : CExpr md) (acc : Std.HashSet Nat),
      convExpr ⟨cx, c, univs, tagSelf N K⟩ tbl e = .ok t →
      ∀ j, j ∈ recurDeps.go shared acc e ↔ j ∈ acc ∨ Frontend.occursConst (K j) t = true := by
  intro e
  induction e with
  | var i =>
    intro t acc h j
    simp only [convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [recurDeps.go, Ix.Kernel.Expr.mkBvar_eq, Frontend.occursConst]
  | sort i =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨l, -, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [recurDeps.go, Frontend.occursConst]
  | ref i us =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨ls, -, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hne : k ≠ K j := by
      unfold ECx.keyAt at hk
      cases ha : c.refs[i.toNat]? with
      | none => simp only [ha] at hk; cases hk
      | some a =>
        simp only [ha] at hk
        exact fresh a k hk j
    simp [recurDeps.go, Frontend.occursConst, hne]
  | recur i us =>
    intro t acc h j
    simp only [convExpr] at h
    unfold tagSelf at h
    by_cases hi : i.toNat < N
    · simp only [hi, ↓reduceIte] at h
      obtain ⟨k, hk, h⟩ := RecordTransfer.bind_ok h
      obtain ⟨ls, -, h⟩ := RecordTransfer.bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h hk
      subst h hk
      simp only [recurDeps.go, Std.HashSet.mem_insert, Frontend.occursConst, beq_iff_eq]
      constructor
      · rintro (h | h)
        · exact .inr (by rw [h])
        · exact .inl h
      · rintro (h | h)
        · exact .inr h
        · exact .inl (inj _ _ h)
    · simp only [hi, ↓reduceIte] at h
      cases h
  | prj i field v ih =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨k, -, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨v', hv, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [recurDeps.go, Frontend.occursConst]
    exact ih v' acc hv j
  | str i =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨b, -, h⟩ := RecordTransfer.bind_ok h
    cases hs : String.fromUTF8? b with
    | none =>
      rw [hs] at h
      cases h
    | some s =>
      rw [hs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [recurDeps.go, Frontend.occursConst]
  | nat i =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨b, -, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [recurDeps.go, Frontend.occursConst]
  | app f a ihf iha =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨f', hf, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨a', ha, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [recurDeps.go, Frontend.occursConst, Bool.or_eq_true]
    rw [iha a' _ ha j, ihf f' acc hf j]
    simp only [or_assoc]
  | lam bc ty b iht ihb =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨ty', hty, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨b', hb, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [recurDeps.go, Frontend.occursConst, Bool.or_eq_true]
    rw [ihb b' _ hb j, iht ty' acc hty j]
    simp only [or_assoc]
  | all bc vc ty b iht ihb =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨ty', hty, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨b', hb, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [recurDeps.go, Frontend.occursConst, Bool.or_eq_true]
    rw [ihb b' _ hb j, iht ty' acc hty j]
    simp only [or_assoc]
  | letE lc ty v b iht ihv ihb =>
    intro t acc h j
    simp only [convExpr] at h
    obtain ⟨ty', hty, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨v', hv, h⟩ := RecordTransfer.bind_ok h
    obtain ⟨b', hb, h⟩ := RecordTransfer.bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [recurDeps.go, Frontend.occursConst, Bool.or_eq_true]
    rw [ihb b' _ hb j, ihv v' _ hv j, iht ty' acc hty j]
    simp only [or_assoc]
  | share i =>
    intro t acc h j
    simp only [convExpr] at h
    cases hr : tbl[i.toNat]? with
    | none => simp only [hr] at h; cases h
    | some r =>
      simp only [hr] at h
      subst h
      have hs : i.toNat < shared.size := by
        rw [agree.1]
        exact (Array.getElem?_eq_some_iff.mp hr).1
      simp only [recurDeps.go, Array.getElem?_eq_getElem hs, Option.getD_some]
      rw [mem_fold_insert, ← getElem!_pos shared i.toNat hs, agree.2 i.toNat t hr j]

theorem fold_agree (inj : ∀ a b, K a = K b → a = b)
    (fresh : ∀ a k, cx.keyAt a = .ok k → ∀ j, k ≠ K j) :
    ∀ (l : List Ixon.Expr) {shared : Array (Std.HashSet Nat)} {tbl : Array (ReadM (CExpr md))},
      Agree K shared tbl →
      Agree K (sharedFold l shared) (RecordTransfer.tblFold ⟨cx, c, univs, tagSelf N K⟩ l tbl)
  | [], _, _, agree => agree
  | entry :: l, shared, tbl, agree => by
    simp only [sharedFold, RecordTransfer.tblFold, List.foldl_cons]
    refine fold_agree inj fresh l ⟨by simp [agree.1], fun i t hi j => ?_⟩
    rw [Array.getElem?_push] at hi
    by_cases hlast : i = tbl.size
    · subst hlast
      simp only [↓reduceIte, Option.some.injEq] at hi
      rw [← agree.1, getElem!_pos (shared.push (recurDeps.go shared {} entry)) shared.size (by simp),
        Array.getElem_push_eq, go_read inj fresh agree entry t {} hi j]
      simp
    · simp only [hlast, ↓reduceIte] at hi
      have hlt : i < tbl.size := (Array.getElem?_eq_some_iff.mp hi).1
      have hpos : i < (shared.push (recurDeps.go shared {} entry)).size := by
        simp [agree.1]; omega
      rw [getElem!_pos (shared.push (recurDeps.go shared {} entry)) i hpos,
        Array.getElem_push_lt (by rw [agree.1]; exact hlt),
        ← getElem!_pos shared i (by rw [agree.1]; exact hlt)]
      exact agree.2 i t hi j

end Tagged

/-- **A member names member `j` by `recur` exactly where its reading mentions `K j`**: the
member reader reading each member `k < N` as `K k`, the keys `K` distinct, and no reference of
the context read as one of them. -/
theorem recurDeps_read {md : Mode} {cx : Ctx md} {c : Ixon.Constant} {param : Nat → LevelParam}
    {N : Nat} {K : Nat → CName md} (inj : ∀ a b, K a = K b → a = b)
    (fresh : ∀ a k, cx.keyAt a = .ok k → ∀ j, k ≠ K j) {d : Ixon.Definition} {type value : CExpr md}
    (htype : (MemberReader.mk' cx c param (tagSelf N K)).read d.typ = .ok type)
    (hvalue : (MemberReader.mk' cx c param (tagSelf N K)).read d.value = .ok value) (j : Nat) :
    j ∈ recurDeps c d ↔ Frontend.occursConst (K j) type = true ∨ Frontend.occursConst (K j) value = true := by
  rw [RecordTransfer.mk'_eq] at htype hvalue
  have agree := fold_agree (c := c) (univs := c.univs.map (convUniv param)) (N := N) inj fresh
    c.sharing.toList (shared := #[]) (tbl := Array.mkEmpty c.sharing.size) ⟨by simp, fun i t hi => by simp at hi⟩
  rw [recurDeps_eq, go_read inj fresh agree _ _ _ hvalue j, go_read inj fresh agree _ _ _ htype j]
  simp

/-! ## Fresh keys -/

/-- How many derivations a key is under. -/
def auxDepth {md : Mode} : Key md → Nat
  | .aux k _ => auxDepth k + 1
  | _ => 0

/-- The deepest key a context's roles bind. -/
def rolesDepth {md : Mode} (cx : Ctx md) : Nat :=
  cx.roles.names.fold (fun m _ k => max m (auxDepth k)) 0

theorem foldl_max_ge {α : Type} (g : α → Nat) :
    ∀ (l : List α) (m : Nat), m ≤ l.foldl (fun m x => max m (g x)) m ∧
      ∀ x ∈ l, g x ≤ l.foldl (fun m x => max m (g x)) m
  | [], m => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | x :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_max_ge g l (max m (g x))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 y hy

theorem role_depth {md : Mode} (cx : Ctx md) {r : ConstRef Address} {k : CName md}
    (h : cx.roles.names[r]? = some k) : auxDepth k ≤ rolesDepth cx := by
  unfold rolesDepth
  rw [Std.HashMap.fold_eq_foldl_toList]
  have hm : (r, k) ∈ cx.roles.names.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
  exact (foldl_max_ge (fun p : ConstRef Address × CName md => auxDepth p.2) _ 0).2 _ hm

theorem keyOfAddress_depth {md : Mode} (cx : Ctx md) {a : Address} {k : CName md}
    (h : keyOfAddress cx.store cx.roles a = some k) : auxDepth k ≤ rolesDepth cx := by
  unfold keyOfAddress at h
  cases hr : resolve cx.store a with
  | none => simp [hr] at h
  | some r =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    cases hk : cx.roles.names[r]? with
    | some k' =>
      simp only [hk, Option.some.injEq] at h
      subst h
      exact role_depth cx hk
    | none =>
      simp only [hk, Option.map_eq_some_iff] at h
      obtain ⟨i, -, rfl⟩ := h
      exact Nat.zero_le _

/-- **Every key a context reads a reference as is at most as deep as its roles' keys.** -/
theorem keyAt_depth {md : Mode} (cx : Ctx md) {a : Address} {k : CName md} (h : cx.keyAt a = .ok k) :
    auxDepth k ≤ rolesDepth cx := by
  unfold Ctx.keyAt at h
  split at h
  · rename_i k' hk'
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact keyOfAddress_depth cx (cx.keys.byAddress_sound a k' hk')
  · split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i k' hk'
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact role_depth cx hk'
      · split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact Nat.zero_le _
        · cases h

/-- A key under `n` derivations. -/
def deepKey {md : Mode} : Nat → Key md
  | 0 => .role default
  | n + 1 => .aux (deepKey n) .model

theorem deepKey_depth {md : Mode} : ∀ n, auxDepth (deepKey (md := md) n) = n
  | 0 => rfl
  | n + 1 => by simp [deepKey, auxDepth, deepKey_depth n]

/-- **Fresh member keys**: member `j` read as a key no reference of `cx` reads as. -/
def freshKey {md : Mode} (cx : Ctx md) (j : Nat) : CName md := .aux (deepKey (rolesDepth cx)) (.member j)

theorem freshKey_inj {md : Mode} (cx : Ctx md) : ∀ a b, freshKey cx a = freshKey cx b → a = b := by
  intro a b h
  simp only [freshKey, Key.aux.injEq, Derived.member.injEq] at h
  exact h.2

theorem freshKey_fresh {md : Mode} (cx : Ctx md) :
    ∀ a k, cx.keyAt a = .ok k → ∀ j, k ≠ freshKey cx j := by
  intro a k h j he
  have := keyAt_depth cx h
  rw [he] at this
  simp only [freshKey, auxDepth, deepKey_depth] at this
  omega

/--
info: 'Ix.Cert.DefinitionOrder.recurDeps_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms recurDeps_read

/--
info: 'Ix.Cert.DefinitionOrder.defOrder_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms defOrder_congr

end Ix.Cert.DefinitionOrder
