module

public import IxC.Kernel.Frontend.InModel

public section

/-!
# The in-model generator's memos are transparent (parametricity, step 2)

The generator's DAG walks (`Frontend/InModel/Kit.lean`, `Nested.lean`) carry a
hash map from a node (and, for the walks under binders, a binder offset) to its
answer. The answer at a node is a function of the node, so a memo whose every
entry is that function's answer leaves the walk's answer that function's: each
walk is its memo-free reading (`*P`), whatever memo it starts from, and returns a
memo of the same kind. Renaming the keys moves the nodes' hashes; after this,
nothing the generator answers reads a hash.
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md : Mode}

/-- **A memo is sound** for `p` when every entry is `p`'s answer. -/
def MemoOk {α β : Type} [BEq α] [Hashable α] (p : α → β) (m : Std.HashMap α β) : Prop :=
  ∀ a b, m[a]? = some b → b = p a

theorem MemoOk.empty {α β : Type} [BEq α] [Hashable α] (p : α → β) :
    MemoOk p (∅ : Std.HashMap α β) := by
  intro a b h
  simp at h

theorem MemoOk.insert {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] {p : α → β}
    {m : Std.HashMap α β} (h : MemoOk p m) (a : α) : MemoOk p (m.insert a (p a)) := by
  intro x b hx
  rw [Std.HashMap.getElem?_insert] at hx
  split at hx
  · rename_i heq
    obtain rfl := eq_of_beq heq
    exact (Option.some.inj hx).symm
  · exact h x b hx

/-- A memo miss: the walk's answer at the node, inserted, keeps the memo sound. -/
theorem MemoOk.miss {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] {p : α → β} {a : α}
    {out : β × Std.HashMap α β} (h : out.1 = p a ∧ MemoOk p out.2) :
    out.1 = p a ∧ MemoOk p (out.2.insert a out.1) :=
  ⟨h.1, by rw [h.1]; exact h.2.insert a⟩

/-- `MemoOk.miss`, with the answer and the memo apart. -/
theorem MemoOk.miss' {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] {p : α → β} {a : α}
    {v : β} {m : Std.HashMap α β} (h1 : v = p a) (h2 : MemoOk p m) :
    v = p a ∧ MemoOk p (m.insert a v) :=
  ⟨h1, by rw [h1]; exact h2.insert a⟩

/-- **`mapMemo` maps**: when each call answers `P` of its element and keeps an
invariant `Q` of the memo, the walk answers the list mapped by `P` and keeps `Q`. -/
theorem mapMemo_spec {α β M : Type} (P : α → β) (Q : M → Prop) (l : List α)
    (f : (x : α) → x ∈ l → M → β × M)
    (hf : ∀ x hx m, Q m → (f x hx m).1 = P x ∧ Q (f x hx m).2) (memo : M) (h : Q memo) :
    (mapMemo l f memo).1 = l.map P ∧ Q (mapMemo l f memo).2 := by
  suffices H : ∀ (l' : List α) (hl : ∀ x ∈ l', x ∈ l) (m : M), Q m →
      (mapMemo.go l f l' hl m).1 = l'.map P ∧ Q (mapMemo.go l f l' hl m).2 from H l _ memo h
  intro l'
  induction l' with
  | nil => intro hl m hm; exact ⟨rfl, hm⟩
  | cons x xs ih =>
    intro hl m hm
    simp only [mapMemo.go]
    obtain ⟨h1, h2⟩ := hf x (hl x List.mem_cons_self) m hm
    obtain ⟨h3, h4⟩ := ih (fun z hz => hl z (List.mem_cons_of_mem _ hz)) _ h2
    exact ⟨by simp only [List.map_cons, h1, h3], h4⟩

/-! ## `mentionsAny` -/

/-- `mentionsAny`, memo-free. -/
def mentionsAnyP (ns : List (Key md)) : Expr md → Bool
  | .bvar _ => false
  | .sort _ => false
  | .lit _ => false
  | .const n _ => ns.contains n
  | .fvar _ ty => mentionsAnyP ns ty
  | .app f a => mentionsAnyP ns f || mentionsAnyP ns a
  | .lam ty b _ => mentionsAnyP ns ty || mentionsAnyP ns b
  | .forallE ty b _ => mentionsAnyP ns ty || mentionsAnyP ns b
  | .letE ty v b _ => mentionsAnyP ns ty || mentionsAnyP ns v || mentionsAnyP ns b
  | .proj s _ x => ns.contains s || mentionsAnyP ns x

theorem mentionsAnyGo_spec (ns : List (Key md)) :
    ∀ (e : Expr md) (memo : Std.HashMap (Expr md) Bool), MemoOk (mentionsAnyP ns) memo →
      (mentionsAnyGo ns memo e).1 = mentionsAnyP ns e ∧
        MemoOk (mentionsAnyP ns) (mentionsAnyGo ns memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo h; exact ⟨rfl, h⟩
  | sort u => intro memo h; exact ⟨rfl, h⟩
  | lit l => intro memo h; exact ⟨rfl, h⟩
  | const n us => intro memo h; exact ⟨rfl, h⟩
  | fvar i ty ih =>
    intro memo h
    simp only [mentionsAnyGo]
    cases hm : memo[Expr.fvar i ty]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.fvar i ty) ?_
      simpa only [mentionsAnyP] using ih memo h
  | app f a ihf iha =>
    intro memo h
    simp only [mentionsAnyGo]
    cases hm : memo[Expr.app f a]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.app f a) ?_
      obtain ⟨hf1, hf2⟩ := ihf memo h
      rcases hgf : mentionsAnyGo ns memo f with ⟨_ | _, m⟩ <;> rw [hgf] at hf1 hf2 <;> dsimp only at hf1 hf2 ⊢
      · obtain ⟨ha1, ha2⟩ := iha m hf2
        exact ⟨by simp only [mentionsAnyP, ← hf1, ha1, Bool.false_or], ha2⟩
      · exact ⟨by simp only [mentionsAnyP, ← hf1, Bool.true_or], hf2⟩
  | lam ty b m iht ihb =>
    intro memo h
    simp only [mentionsAnyGo]
    cases hm : memo[Expr.lam ty b m]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.lam ty b m) ?_
      obtain ⟨ht1, ht2⟩ := iht memo h
      rcases hgt : mentionsAnyGo ns memo ty with ⟨_ | _, m'⟩ <;> rw [hgt] at ht1 ht2 <;> dsimp only at ht1 ht2 ⊢
      · obtain ⟨hb1, hb2⟩ := ihb m' ht2
        exact ⟨by simp only [mentionsAnyP, ← ht1, hb1, Bool.false_or], hb2⟩
      · exact ⟨by simp only [mentionsAnyP, ← ht1, Bool.true_or], ht2⟩
  | forallE ty b m iht ihb =>
    intro memo h
    simp only [mentionsAnyGo]
    cases hm : memo[Expr.forallE ty b m]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.forallE ty b m) ?_
      obtain ⟨ht1, ht2⟩ := iht memo h
      rcases hgt : mentionsAnyGo ns memo ty with ⟨_ | _, m'⟩ <;> rw [hgt] at ht1 ht2 <;> dsimp only at ht1 ht2 ⊢
      · obtain ⟨hb1, hb2⟩ := ihb m' ht2
        exact ⟨by simp only [mentionsAnyP, ← ht1, hb1, Bool.false_or], hb2⟩
      · exact ⟨by simp only [mentionsAnyP, ← ht1, Bool.true_or], ht2⟩
  | letE ty v b l iht ihv ihb =>
    intro memo h
    simp only [mentionsAnyGo]
    cases hm : memo[Expr.letE ty v b l]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.letE ty v b l) ?_
      obtain ⟨ht1, ht2⟩ := iht memo h
      rcases hgt : mentionsAnyGo ns memo ty with ⟨_ | _, m1⟩ <;> rw [hgt] at ht1 ht2 <;> dsimp only at ht1 ht2 ⊢
      · obtain ⟨hv1, hv2⟩ := ihv m1 ht2
        rcases hgv : mentionsAnyGo ns m1 v with ⟨_ | _, m2⟩ <;> rw [hgv] at hv1 hv2 <;> dsimp only at hv1 hv2 ⊢
        · obtain ⟨hb1, hb2⟩ := ihb m2 hv2
          exact ⟨by simp only [mentionsAnyP, ← ht1, ← hv1, hb1, Bool.false_or], hb2⟩
        · exact ⟨by simp only [mentionsAnyP, ← ht1, ← hv1, Bool.false_or, Bool.true_or], hv2⟩
      · exact ⟨by simp only [mentionsAnyP, ← ht1, Bool.true_or], ht2⟩
  | proj s i x ih =>
    intro memo h
    simp only [mentionsAnyGo]
    cases hm : memo[Expr.proj s i x]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.proj s i x) ?_
      by_cases hs : ns.contains s = true
      · simp only [hs, if_true, mentionsAnyP, Bool.true_or]; exact ⟨trivial, h⟩
      · simp only [hs, mentionsAnyP, Bool.false_or]
        exact ih memo h

theorem mentionsAny_eq (ns : List (Key md)) (e : Expr md) : mentionsAny ns e = mentionsAnyP ns e :=
  (mentionsAnyGo_spec ns e ∅ (MemoOk.empty _)).1

/-! ## `maxHeight` -/

/-- `maxHeightGo`'s answer, memo-free. -/
def maxHeightP (heights : Key md → Nat) : Expr md → Nat
  | .const n _ => heights n
  | .bvar _ => 0
  | .sort _ => 0
  | .lit _ => 0
  | .fvar _ ty => maxHeightP heights ty
  | .app f a => max (maxHeightP heights f) (maxHeightP heights a)
  | .lam ty b _ => max (maxHeightP heights ty) (maxHeightP heights b)
  | .forallE ty b _ => max (maxHeightP heights ty) (maxHeightP heights b)
  | .letE ty v b _ =>
    max (maxHeightP heights ty) (max (maxHeightP heights v) (maxHeightP heights b))
  | .proj _ _ x => maxHeightP heights x

theorem maxHeightGo_spec (heights : Key md → Nat) :
    ∀ (e : Expr md) (memo : Std.HashMap (Expr md) Nat), MemoOk (maxHeightP heights) memo →
      (maxHeightGo heights memo e).1 = maxHeightP heights e ∧
        MemoOk (maxHeightP heights) (maxHeightGo heights memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo h; exact ⟨rfl, h⟩
  | sort u => intro memo h; exact ⟨rfl, h⟩
  | lit l => intro memo h; exact ⟨rfl, h⟩
  | const n us => intro memo h; exact ⟨rfl, h⟩
  | fvar i ty ih =>
    intro memo h
    simp only [maxHeightGo]
    cases hm : memo[Expr.fvar i ty]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.fvar i ty) ?_
      simpa only [maxHeightP] using ih memo h
  | app f a ihf iha =>
    intro memo h
    simp only [maxHeightGo]
    cases hm : memo[Expr.app f a]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := ihf memo h
      obtain ⟨h3, h4⟩ := iha _ h2
      exact MemoOk.miss' (by simp only [maxHeightP, h1, h3]) h4
  | lam ty b m iht ihb =>
    intro memo h
    simp only [maxHeightGo]
    cases hm : memo[Expr.lam ty b m]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := iht memo h
      obtain ⟨h3, h4⟩ := ihb _ h2
      exact MemoOk.miss' (by simp only [maxHeightP, h1, h3]) h4
  | forallE ty b m iht ihb =>
    intro memo h
    simp only [maxHeightGo]
    cases hm : memo[Expr.forallE ty b m]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := iht memo h
      obtain ⟨h3, h4⟩ := ihb _ h2
      exact MemoOk.miss' (by simp only [maxHeightP, h1, h3]) h4
  | letE ty v b l iht ihv ihb =>
    intro memo h
    simp only [maxHeightGo]
    cases hm : memo[Expr.letE ty v b l]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := iht memo h
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      exact MemoOk.miss' (by simp only [maxHeightP, h1, h3, h5]) h6
  | proj s i x ih =>
    intro memo h
    simp only [maxHeightGo]
    cases hm : memo[Expr.proj s i x]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss (a := Expr.proj s i x) ?_
      simpa only [maxHeightP] using ih memo h

theorem maxHeight_eq (heights : Key md → Nat) (e : Expr md) :
    maxHeight heights e = maxHeightP heights e :=
  (maxHeightGo_spec heights e ∅ (MemoOk.empty _)).1

/-! ## `substParams` -/

/-- `substParams.go`'s answer at cursor `k`, memo-free. -/
def substParamsP (d n : Nat) (vals : List (Expr md)) (k : Nat) : Expr md → Expr md
  | .bvar i =>
    if i < d + k then .bvar i
    else if i < d + k + n then (vals.getD (n - 1 - (i - d - k)) default).liftLooseBVars k 0
    else .bvar (i - n)
  | .sort u => .sort u
  | .const nm us => .const nm us
  | .lit l => .lit l
  | .app f a => .app (substParamsP d n vals k f) (substParamsP d n vals k a)
  | .lam t b m => .lam (substParamsP d n vals k t) (substParamsP d n vals (k + 1) b) m
  | .forallE t b m => .forallE (substParamsP d n vals k t) (substParamsP d n vals (k + 1) b) m
  | .letE t v b l =>
    .letE (substParamsP d n vals k t) (substParamsP d n vals k v) (substParamsP d n vals (k + 1) b) l
  | .proj s i x => .proj s i (substParamsP d n vals k x)
  | .fvar i t => .fvar i (substParamsP d n vals k t)

theorem substParams_go_spec (d n : Nat) (vals : List (Expr md)) :
    ∀ (e : Expr md) (k : Nat) (memo : Std.HashMap (Expr md × Nat) (Expr md)),
      MemoOk (fun q => substParamsP d n vals q.2 q.1) memo →
      (substParams.go d n vals memo k e).1 = substParamsP d n vals k e ∧
        MemoOk (fun q => substParamsP d n vals q.2 q.1) (substParams.go d n vals memo k e).2 := by
  intro e
  induction e with
  | bvar i => intro k memo h; exact ⟨rfl, h⟩
  | sort u => intro k memo h; exact ⟨rfl, h⟩
  | lit l => intro k memo h; exact ⟨rfl, h⟩
  | const nm us => intro k memo h; exact ⟨rfl, h⟩
  | fvar i t ih =>
    intro k memo h
    simp only [substParams.go]
    cases hm : memo[(Expr.fvar i t, k)]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := ih k memo h
      exact MemoOk.miss' (a := (Expr.fvar i t, k)) (by simp only [substParamsP, h1]) h2
  | app f a ihf iha =>
    intro k memo h
    simp only [substParams.go]
    cases hm : memo[(Expr.app f a, k)]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := ihf k memo h
      obtain ⟨h3, h4⟩ := iha k _ h2
      exact MemoOk.miss' (a := (Expr.app f a, k)) (by simp only [substParamsP, h1, h3]) h4
  | lam t b m iht ihb =>
    intro k memo h
    simp only [substParams.go]
    cases hm : memo[(Expr.lam t b m, k)]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := iht k memo h
      obtain ⟨h3, h4⟩ := ihb (k + 1) _ h2
      exact MemoOk.miss' (a := (Expr.lam t b m, k)) (by simp only [substParamsP, h1, h3]) h4
  | forallE t b m iht ihb =>
    intro k memo h
    simp only [substParams.go]
    cases hm : memo[(Expr.forallE t b m, k)]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := iht k memo h
      obtain ⟨h3, h4⟩ := ihb (k + 1) _ h2
      exact MemoOk.miss' (a := (Expr.forallE t b m, k)) (by simp only [substParamsP, h1, h3]) h4
  | letE t v b l iht ihv ihb =>
    intro k memo h
    simp only [substParams.go]
    cases hm : memo[(Expr.letE t v b l, k)]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := iht k memo h
      obtain ⟨h3, h4⟩ := ihv k _ h2
      obtain ⟨h5, h6⟩ := ihb (k + 1) _ h4
      exact MemoOk.miss' (a := (Expr.letE t v b l, k)) (by simp only [substParamsP, h1, h3, h5]) h6
  | proj s i x ih =>
    intro k memo h
    simp only [substParams.go]
    cases hm : memo[(Expr.proj s i x, k)]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := ih k memo h
      exact MemoOk.miss' (a := (Expr.proj s i x, k)) (by simp only [substParamsP, h1]) h2

theorem substParams_eq (d n : Nat) (vals : List (Expr md)) (e : Expr md) :
    substParams d n vals e = substParamsP d n vals 0 e :=
  (substParams_go_spec d n vals e 0 ∅ (MemoOk.empty _)).1

/-! ## `specFam` -/

/-- `specFamGo`'s answer, memo-free (its argument walks through `mapMemo` at a
trivial memo, as the walk's own). -/
def specFamP (T : Key md) (lps : List LevelParam) (nP : Nat)
    (members : List (Key md × Nat × Nat)) : Expr md → Expr md
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .fvar i t => .fvar i t
  | .lit l => .lit l
  | .const n us =>
    match members.find? (·.1 == n) with
    | some (_, m, nIdx) =>
      if nP + nIdx == 0 && us == lps.map .param then
        Expr.mkAppN (constP (auxName T) lps) [constP (tagCtorName T m) lps]
      else .const n us
    | none => .const n us
  | .app g x =>
    let f := (Expr.app g x).getAppFn
    let args := (Expr.app g x).getAppArgs
    let walkArgs (as : List (Expr md)) (has : ∀ y ∈ as, y ∈ args) : List (Expr md) :=
      (mapMemo as (fun y hy (_ : Unit) =>
        have : sizeOf y < sizeOf (Expr.app g x) := sizeOf_lt_of_mem_getAppArgs (has y hy)
        (specFamP T lps nP members y, ())) ()).1
    match f with
    | .const n us =>
      match members.find? (·.1 == n) with
      | some (_, m, nIdx) =>
        if args.length == nP + nIdx && us == lps.map .param then
          let ps := walkArgs (args.take nP) (fun _ h => List.mem_of_mem_take h)
          let is := walkArgs (args.drop nP) (fun _ h => List.mem_of_mem_drop h)
          Expr.mkAppN (constP (auxName T) lps)
            (ps ++ [Expr.mkAppN (constP (tagCtorName T m) lps) (ps ++ is)])
        else
          have : sizeOf f < sizeOf (Expr.app g x) := sizeOf_getAppFn_app g x
          Expr.mkAppN (specFamP T lps nP members f) (walkArgs args (fun _ h => h))
      | none => Expr.mkAppN f (walkArgs args (fun _ h => h))
    | _ =>
      have : sizeOf f < sizeOf (Expr.app g x) := sizeOf_getAppFn_app g x
      Expr.mkAppN (specFamP T lps nP members f) (walkArgs args (fun _ h => h))
  | .lam d b m => .lam (specFamP T lps nP members d) (specFamP T lps nP members b) m
  | .forallE d b m => .forallE (specFamP T lps nP members d) (specFamP T lps nP members b) m
  | .letE t v b l =>
    .letE (specFamP T lps nP members t) (specFamP T lps nP members v) (specFamP T lps nP members b) l
  | .proj s i x => .proj s i (specFamP T lps nP members x)
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (subst_vars; simp only [Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec,
        Expr.forallE.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec] at *; omega)
    | (subst_vars; assumption)
    | omega

/-- A trivial-memo `mapMemo` is `List.map`. -/
theorem mapMemo_unit {α β : Type} (P : α → β) (l : List α) (f : (x : α) → x ∈ l → Unit → β × Unit)
    (hf : ∀ x hx, (f x hx ()).1 = P x) : (mapMemo l f ()).1 = l.map P :=
  (mapMemo_spec P (fun _ => True) l f (fun x hx m _ => ⟨by cases m; exact hf x hx, trivial⟩) () trivial).1

/-- `mapMemo_unit` at a constant answer function. -/
theorem mapMemo_unit_map {α β : Type} (P : α → β) (l : List α) :
    (mapMemo l (fun y _ (_ : Unit) => (P y, ())) ()).1 = l.map P :=
  mapMemo_unit P l _ (fun _ _ => rfl)

theorem specFamGo_spec (T : Key md) (lps : List LevelParam) (nP : Nat)
    (members : List (Key md × Nat × Nat)) :
    ∀ (e : Expr md) (memo : Std.HashMap (Expr md) (Expr md)),
    MemoOk (specFamP T lps nP members) memo →
    (specFamGo T lps nP members memo e).1 = specFamP T lps nP members e ∧
      MemoOk (specFamP T lps nP members) (specFamGo T lps nP members memo e).2
  | .bvar i, memo, h => by rw [specFamGo, specFamP]; exact ⟨rfl, h⟩
  | .sort u, memo, h => by rw [specFamGo, specFamP]; exact ⟨rfl, h⟩
  | .fvar i t, memo, h => by rw [specFamGo, specFamP]; exact ⟨rfl, h⟩
  | .lit l, memo, h => by rw [specFamGo, specFamP]; exact ⟨rfl, h⟩
  | .const n us, memo, h => by
    rw [specFamGo, specFamP]
    split
    · rename_i heq
      simp only [heq]
      split <;> exact ⟨by first | trivial | rfl, h⟩
    · rename_i heq
      simp only [heq]
      exact ⟨by first | trivial | rfl, h⟩
  | .app g x, memo, h => by
    rw [specFamGo]
    cases hm : memo[g.app x]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      refine MemoOk.miss ?_
      rw [specFamP]
      simp only [mapMemo_unit_map]
      have IH : ∀ (l : List (Expr md)), (∀ y ∈ l, y ∈ (Expr.app g x).getAppArgs) →
          ∀ m, MemoOk (specFamP T lps nP members) m →
          (mapMemo l (fun y _ m => specFamGo T lps nP members m y) m).1 = l.map (specFamP T lps nP members) ∧
            MemoOk (specFamP T lps nP members) (mapMemo l (fun y _ m => specFamGo T lps nP members m y) m).2 :=
        fun l hl m hm => mapMemo_spec _ _ l _ (fun y hy m hm =>
          have : sizeOf y < sizeOf (Expr.app g x) := sizeOf_lt_of_mem_getAppArgs (hl y hy)
          specFamGo_spec T lps nP members y m hm) m hm
      have IHf : ∀ m, MemoOk (specFamP T lps nP members) m →
          (specFamGo T lps nP members m (Expr.app g x).getAppFn).1 =
            specFamP T lps nP members (Expr.app g x).getAppFn ∧
          MemoOk (specFamP T lps nP members) (specFamGo T lps nP members m (Expr.app g x).getAppFn).2 :=
        fun m hm =>
          have : sizeOf (Expr.app g x).getAppFn < sizeOf (Expr.app g x) := sizeOf_getAppFn_app g x
          specFamGo_spec T lps nP members _ m hm
      split
      · rename_i heq
        simp only [heq]
        split
        · rename_i heq2
          simp only [heq2]
          split
          · obtain ⟨h1, h2⟩ := IH _ (fun _ h => List.mem_of_mem_take h) memo h
            obtain ⟨h3, h4⟩ := IH _ (fun _ h => List.mem_of_mem_drop h) _ h2
            exact ⟨by rw [h1, h3], h4⟩
          · obtain ⟨h1, h2⟩ := IHf memo h
            obtain ⟨h3, h4⟩ := IH _ (fun _ h => h) _ h2
            refine ⟨?_, by simpa only [heq] using h4⟩
            rw [← heq, h1, h3]
        · rename_i heq2
          simp only [heq2]
          obtain ⟨h1, h2⟩ := IH _ (fun _ h => h) memo h
          exact ⟨by rw [h1], h2⟩
      · rename_i hnc
        obtain ⟨h1, h2⟩ := IHf memo h
        obtain ⟨h3, h4⟩ := IH _ (fun _ h => h) _ h2
        split
        · rename_i heq
          exact (hnc _ _ heq).elim
        · exact ⟨by rw [h1, h3], h4⟩
  | .lam d b m, memo, h => by
    rw [specFamGo]
    cases hm : memo[Expr.lam d b m]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := specFamGo_spec T lps nP members d memo h
      obtain ⟨h3, h4⟩ := specFamGo_spec T lps nP members b _ h2
      exact MemoOk.miss' (by rw [specFamP, h1, h3]) h4
  | .forallE d b m, memo, h => by
    rw [specFamGo]
    cases hm : memo[Expr.forallE d b m]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := specFamGo_spec T lps nP members d memo h
      obtain ⟨h3, h4⟩ := specFamGo_spec T lps nP members b _ h2
      exact MemoOk.miss' (by rw [specFamP, h1, h3]) h4
  | .letE t v b l, memo, h => by
    rw [specFamGo]
    cases hm : memo[Expr.letE t v b l]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := specFamGo_spec T lps nP members t memo h
      obtain ⟨h3, h4⟩ := specFamGo_spec T lps nP members v _ h2
      obtain ⟨h5, h6⟩ := specFamGo_spec T lps nP members b _ h4
      exact MemoOk.miss' (by rw [specFamP, h1, h3, h5]) h6
  | .proj s i x, memo, h => by
    rw [specFamGo]
    cases hm : memo[Expr.proj s i x]? with
    | some r => exact ⟨h _ _ hm, h⟩
    | none =>
      dsimp only
      obtain ⟨h1, h2⟩ := specFamGo_spec T lps nP members x memo h
      exact MemoOk.miss' (by rw [specFamP, h1]) h2
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | assumption
    | (simp only [Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec, Expr.letE.sizeOf_spec,
        Expr.proj.sizeOf_spec]; omega)
    | omega

theorem specFam_eq (T : Key md) (lps : List LevelParam) (nP : Nat)
    (members : List (Key md × Nat × Nat)) (e : Expr md) :
    specFam T lps nP members e = specFamP T lps nP members e :=
  (specFamGo_spec T lps nP members e ∅ (MemoOk.empty _)).1

/-! ## `specAll` -/

/-- `specAllGo`'s answer at offset `o`, memo-free. -/
def specAllP (fam : Family md) (o : Nat) (e : Expr md) : Expr md :=
  match hc : matchCarrier fam o e with
  | some (tag, idx) =>
    auxAt fam tag o (mapMemo idx (fun y hy (_ : Unit) =>
      have : sizeOf y < sizeOf e := sizeOf_lt_of_mem_getAppArgs (matchCarrier_args hc y hy)
      (specAllP fam o y, ())) ()).1
  | none =>
    match e with
    | .app f a => .app (specAllP fam o f) (specAllP fam o a)
    | .lam d b m => .lam (specAllP fam o d) (specAllP fam (o + 1) b) m
    | .forallE d b m => .forallE (specAllP fam o d) (specAllP fam (o + 1) b) m
    | .letE t v b l => .letE (specAllP fam o t) (specAllP fam o v) (specAllP fam (o + 1) b) l
    | .proj s i x => .proj s i (specAllP fam o x)
    | e => e
termination_by sizeOf e
decreasing_by
  all_goals first
    | assumption
    | (subst_vars; simp only [Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec,
        Expr.forallE.sizeOf_spec, Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec] at *; omega)
    | omega

theorem specAllP_some {fam : Family md} {o : Nat} {e : Expr md} {tag : Nat} {idx : List (Expr md)}
    (hc : matchCarrier fam o e = some (tag, idx)) :
    specAllP fam o e = auxAt fam tag o (idx.map (specAllP fam o)) := by
  rw [specAllP]
  split
  · rename_i tag' idx' hc'
    rw [hc] at hc'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc')
    simp only [mapMemo_unit_map]
  · rename_i hc'
    rw [hc] at hc'
    cases hc'

theorem specAllP_none {fam : Family md} {o : Nat} {e : Expr md} (hc : matchCarrier fam o e = none) :
    specAllP fam o e =
      match e with
      | .app f a => .app (specAllP fam o f) (specAllP fam o a)
      | .lam d b m => .lam (specAllP fam o d) (specAllP fam (o + 1) b) m
      | .forallE d b m => .forallE (specAllP fam o d) (specAllP fam (o + 1) b) m
      | .letE t v b l => .letE (specAllP fam o t) (specAllP fam o v) (specAllP fam (o + 1) b) l
      | .proj s i x => .proj s i (specAllP fam o x)
      | e => e := by
  rw [specAllP]
  split
  · rename_i tag' idx' hc'
    rw [hc] at hc'
    cases hc'
  · rfl

theorem specAllGo_spec (fam : Family md) (e : Expr md) (o : Nat)
    (memo : Std.HashMap (Expr md × Nat) (Expr md))
    (h : MemoOk (fun q => specAllP fam q.2 q.1) memo) :
    (specAllGo fam memo o e).1 = specAllP fam o e ∧
      MemoOk (fun q => specAllP fam q.2 q.1) (specAllGo fam memo o e).2 := by
  rcases hcar : matchCarrier fam o e with _ | ⟨tag, idx⟩
  · cases e with
    | bvar i =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · exact ⟨(specAllP_none hcar).symm, h⟩
    | sort u =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · exact ⟨(specAllP_none hcar).symm, h⟩
    | fvar i t =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · exact ⟨(specAllP_none hcar).symm, h⟩
    | const n us =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · exact ⟨(specAllP_none hcar).symm, h⟩
    | lit l =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · exact ⟨(specAllP_none hcar).symm, h⟩
    | app f a =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · dsimp only
        cases hm : memo[(Expr.app f a, o)]? with
        | some r => exact ⟨h _ _ hm, h⟩
        | none =>
          dsimp only
          obtain ⟨h1, h2⟩ := specAllGo_spec fam f o memo h
          obtain ⟨h3, h4⟩ := specAllGo_spec fam a o _ h2
          exact MemoOk.miss' (a := (Expr.app f a, o)) (by simp only [specAllP_none hcar, h1, h3]) h4
    | lam d b m =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · dsimp only
        cases hm : memo[(Expr.lam d b m, o)]? with
        | some r => exact ⟨h _ _ hm, h⟩
        | none =>
          dsimp only
          obtain ⟨h1, h2⟩ := specAllGo_spec fam d o memo h
          obtain ⟨h3, h4⟩ := specAllGo_spec fam b (o + 1) _ h2
          exact MemoOk.miss' (a := (Expr.lam d b m, o)) (by simp only [specAllP_none hcar, h1, h3]) h4
    | forallE d b m =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · dsimp only
        cases hm : memo[(Expr.forallE d b m, o)]? with
        | some r => exact ⟨h _ _ hm, h⟩
        | none =>
          dsimp only
          obtain ⟨h1, h2⟩ := specAllGo_spec fam d o memo h
          obtain ⟨h3, h4⟩ := specAllGo_spec fam b (o + 1) _ h2
          exact MemoOk.miss' (a := (Expr.forallE d b m, o)) (by simp only [specAllP_none hcar, h1, h3]) h4
    | letE t v b l =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · dsimp only
        cases hm : memo[(Expr.letE t v b l, o)]? with
        | some r => exact ⟨h _ _ hm, h⟩
        | none =>
          dsimp only
          obtain ⟨h1, h2⟩ := specAllGo_spec fam t o memo h
          obtain ⟨h3, h4⟩ := specAllGo_spec fam v o _ h2
          obtain ⟨h5, h6⟩ := specAllGo_spec fam b (o + 1) _ h4
          exact MemoOk.miss' (a := (Expr.letE t v b l, o)) (by simp only [specAllP_none hcar, h1, h3, h5]) h6
    | proj s i x =>
      rw [specAllGo]
      split
      · rename_i hc'; rw [hcar] at hc'; cases hc'
      · dsimp only
        cases hm : memo[(Expr.proj s i x, o)]? with
        | some r => exact ⟨h _ _ hm, h⟩
        | none =>
          dsimp only
          obtain ⟨h1, h2⟩ := specAllGo_spec fam x o memo h
          exact MemoOk.miss' (a := (Expr.proj s i x, o)) (by simp only [specAllP_none hcar, h1]) h2
  · rw [specAllP_some hcar, specAllGo]
    split
    · rename_i tag' idx' hc'
      rw [hcar] at hc'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc')
      dsimp only
      obtain ⟨h1, h2⟩ := mapMemo_spec (specAllP fam o) (MemoOk (fun q => specAllP fam q.2 q.1)) idx _
        (fun y hy m hm =>
          have : sizeOf y < sizeOf e := sizeOf_lt_of_mem_getAppArgs (matchCarrier_args hcar y hy)
          specAllGo_spec fam y o m hm) memo h
      exact ⟨by rw [h1], h2⟩
    · rename_i hc'; rw [hcar] at hc'; cases hc'
termination_by sizeOf e
decreasing_by
  all_goals first
    | assumption
    | (simp only [Expr.app.sizeOf_spec, Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec,
        Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec]; omega)
    | omega

theorem specAll_eq (fam : Family md) (o : Nat) (e : Expr md) : specAll fam o e = specAllP fam o e :=
  (specAllGo_spec fam e o ∅ (MemoOk.empty _)).1

end Ix.Kernel.Frontend.InModel
