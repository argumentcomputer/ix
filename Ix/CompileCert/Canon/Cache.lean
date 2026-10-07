import Ix.CompileCert.Canon.Rel

/-!
# M7 L1: the strong-result cache returns the comparator's own results

`compareConst` (and through it `compareInd`, `compareCtor`) runs in `CmpM`: a state whose
cache maps the unordered name pair (with the external mode) to an ordering and the name that
was on the left when it was computed. Design document §3.2 ("Strength") and §3.4 C2/C3:
caching strong results across the rounds of one refinement is sound provided the cached value
is read back in the orientation it was stored in.

This module proves it for `portFixes := true` (`Rules.compiler`):

* `Coh A ms st`: every cache entry is the true strong result of two entries (members, or
  constructors with their inductives' level lists) of the component `ms`, under every context
  of the run `A` (same level rule, address map and in-block names; any class indices);
* the cached comparisons return exactly the pure ones and keep `Coh`
  (`compareCtor_sim` … `compareConst_sim`), given `NameInj ms` (the component's member and
  constructor names identify their entries under `==`, as Lean's names do) and
  `AddrCongr A.addr?`;
* hence `compareFresh` (a comparison from the empty cache) equals the pure comparison
  (`compareFresh_eq`) and is a total preorder on the component (`compareFresh_total`).

The defect C2 of the Lean port (`portFixes := false`, `Rules.today`) is exhibited by
`cacheGet_today_reversed`: a stored strong `lt` for `(x, y)` is read back as `lt` for
`(y, x)`.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr MutConst Def Ind Rec ConstructorVal RecursorVal RecursorRule MutCtx)

/-! ## `==` on names and on cache keys -/

instance equivBEq_name : EquivBEq Name where
  rfl := name_beq_refl _
  symm h := name_beq_symm h
  trans h1 h2 := name_beq_trans h1 h2

instance lawfulHashable_name : LawfulHashable Name where
  hash_eq a b h := by
    show hash a.getHash = hash b.getHash
    rw [name_beq_iff.1 h]

instance equivBEq_prod {α β : Type} [BEq α] [BEq β] [EquivBEq α] [EquivBEq β] :
    EquivBEq (α × β) where
  rfl {a} := by
    obtain ⟨x, y⟩ := a
    show (x == x && y == y) = true
    simp
  symm {a b} h := by
    obtain ⟨x, y⟩ := a; obtain ⟨x', y'⟩ := b
    change (x == x' && y == y') = true at h
    show (x' == x && y' == y) = true
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨BEq.symm h.1, BEq.symm h.2⟩
  trans {a b c} h1 h2 := by
    obtain ⟨x, y⟩ := a; obtain ⟨x', y'⟩ := b; obtain ⟨x'', y''⟩ := c
    change (x == x' && y == y') = true at h1
    change (x' == x'' && y' == y'') = true at h2
    show (x == x'' && y == y'') = true
    simp only [Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨BEq.trans h1.1 h2.1, BEq.trans h1.2 h2.2⟩

instance lawfulHashable_prod {α β : Type} [BEq α] [BEq β] [Hashable α] [Hashable β]
    [LawfulHashable α] [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq a b h := by
    obtain ⟨x, y⟩ := a; obtain ⟨x', y'⟩ := b
    change (x == x' && y == y') = true at h
    simp only [Bool.and_eq_true] at h
    have h1 : hash x = hash x' := LawfulHashable.hash_eq x x' h.1
    have h2 : hash y = hash y' := LawfulHashable.hash_eq y y' h.2
    show mixHash (hash x) (hash y) = mixHash (hash x') (hash y')
    rw [h1, h2]

theorem prod_beq_iff {α β : Type} [BEq α] [BEq β] (a b : α × β) :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true := by
  obtain ⟨x, y⟩ := a; obtain ⟨x', y'⟩ := b
  show (x == x' && y == y') = true ↔ _
  simp

theorem cacheKey_fst (b : Bool) (x y : Name) : (cacheKey b x y).1 = b := by
  unfold cacheKey; split <;> rfl

/-- Two cache keys that are `==` name the same unordered pair. -/
theorem cacheKey_beq {x y x' y' : Name} {b : Bool}
    (h : (cacheKey b x y == cacheKey b x' y') = true) :
    ((x == x') = true ∧ (y == y') = true) ∨ ((x == y') = true ∧ (y == x') = true) := by
  unfold cacheKey at h
  split at h <;> split at h <;> simp only [prod_beq_iff] at h <;> obtain ⟨-, h1, h2⟩ := h
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨h1, h2⟩
  · exact .inr ⟨h2, h1⟩
  · exact .inl ⟨h2, h1⟩

/-! ## The component's entries -/

/-- An entry of a component's name table: a member, or a constructor of a member. -/
inductive Ent where
  | mem (m : MutConst)
  | ctor (m : MutConst) (cv : ConstructorVal)

def Ent.name : Ent → Name
  | .mem m => m.name
  | .ctor _ cv => cv.cnst.name

/-- The entries of a component: each member, then its constructors. -/
def ents (ms : List MutConst) : List Ent :=
  ms.flatMap fun m => .mem m :: m.ctors.toList.map (.ctor m)

theorem mem_ents_mem {ms : List MutConst} {m : MutConst} (h : m ∈ ms) : Ent.mem m ∈ ents ms := by
  simp only [ents, List.mem_flatMap]; exact ⟨m, h, by simp⟩

theorem mem_ents_ctor {ms : List MutConst} {m : MutConst} (h : m ∈ ms) {cv : ConstructorVal}
    (hc : cv ∈ m.ctors) : Ent.ctor m cv ∈ ents ms := by
  simp only [ents, List.mem_flatMap]; exact ⟨m, h, by simpa using hc⟩

/-- The component's member and constructor names identify their entries (Lean's names are
unique; `Ix.Name`'s `==` is hash equality). -/
def NameInj (ms : List MutConst) : Prop :=
  ∀ e₁ ∈ ents ms, ∀ e₂ ∈ ents ms, (e₁.name == e₂.name) = true → e₁ = e₂

/-- The pure comparison of two entries. -/
def entP (c : CmpCtx) : Ent → Ent → Except String SOrder
  | .mem x, .mem y => constP c x y
  | .ctor mx x, .ctor my y => ctorP c mx.levelParams.toList my.levelParams.toList x y
  | _, _ => .error "entP: kinds"

theorem entP_swap {c : CmpCtx} (hc : AddrCongr c.addr?) {e₁ e₂ : Ent} {s o}
    (h : entP c e₁ e₂ = .ok ⟨s, o⟩) : entP c e₂ e₁ = .ok ⟨s, o.swap⟩ := by
  cases e₁ <;> cases e₂ <;> simp only [entP] at h ⊢
  · exact (constP_total c hc).swap trivial trivial h
  · cases h
  · cases h
  · exact (ctorP_total c hc).swap (a := (_, _)) (b := (_, _)) trivial trivial h

theorem entP_strong {c c' : CmpCtx} (hd : SameDom c c') {e₁ e₂ : Ent} {o}
    (h : entP c e₁ e₂ = .ok ⟨true, o⟩) : entP c' e₁ e₂ = .ok ⟨true, o⟩ := by
  cases e₁ <;> cases e₂ <;> simp only [entP] at h ⊢
  · exact constP_strong hd _ _ _ h
  · cases h
  · cases h
  · exact ctorP_strong hd _ _ _ _ _ h

/-! ## Runs and coherent caches -/

/-- What every round of one refinement shares: the rule set, the address map, and the names
in the block. -/
structure Run where
  rules : Rules
  addr? : Name → Option Address
  dom : Name → Bool

/-- A context of the run, in the external mode of the cache flag `b`. -/
def Run.Adm (A : Run) (b : Bool) (c : CmpCtx) : Prop :=
  c.levels = A.rules.levels ∧ c.addr? = A.addr? ∧ c.mode = (if b then .blind else .addr) ∧
    ∀ n, (c.mutCtx[n]?).isSome = A.dom n

theorem Run.Adm.sameDom {A : Run} {b} {c c' : CmpCtx} (h : A.Adm b c) (h' : A.Adm b c') :
    SameDom c c' where
  levels := h.1.trans h'.1.symm
  mode := h.2.2.1.trans h'.2.2.1.symm
  addr := h.2.1.trans h'.2.1.symm
  dom n := (h.2.2.2 n).trans (h'.2.2.2 n).symm

theorem Run.Adm.addr {A : Run} {b} {c : CmpCtx} (h : A.Adm b c) (hA : AddrCongr A.addr?) :
    AddrCongr c.addr? := by rw [h.2.1]; exact hA

/-- Every cache entry is a true strong result of two entries of the component under every
context of the run. -/
def Coh (A : Run) (ms : List MutConst) (st : CmpState) : Prop :=
  ∀ (k : Bool × Name × Name) (v : Ordering × Name), st.cache[k]? = some v →
    ∃ e₁ ∈ ents ms, ∃ e₂ ∈ ents ms, (v.2 == e₁.name) = true ∧
      (k == cacheKey k.1 e₁.name e₂.name) = true ∧
      ∀ c, A.Adm k.1 c → entP c e₁ e₂ = .ok ⟨true, v.1⟩

theorem coh_empty (A : Run) (ms : List MutConst) : Coh A ms {} := by
  intro k v h
  simp at h

theorem coh_counters {A : Run} {ms} {st : CmpState} (h : Coh A ms st) (hz ad : Nat) :
    Coh A ms { st with hazards := hz, addrDecided := ad } := h

/-! ## Simulation of a cached computation by a pure one -/

/-- `m`, run from any state satisfying `Inv`, returns what `r` returns and ends in a state
satisfying `Inv`. -/
def Sim (Inv : CmpState → Prop) {α : Type} (m : CmpM α) (r : Except String α) : Prop :=
  ∀ st, Inv st → ∃ st', Inv st' ∧ m.run st = r.map (fun a => (a, st'))

namespace Sim

variable {Inv : CmpState → Prop} {α β : Type}

theorem pure' (a : α) : Sim Inv (pure a) (pure a) := fun st h => ⟨st, h, rfl⟩

theorem bind {m : CmpM α} {r : Except String α} {k : α → CmpM β} {k' : α → Except String β}
    (hm : Sim Inv m r) (hk : ∀ a, r = .ok a → Sim Inv (k a) (k' a)) :
    Sim Inv (m >>= k) (r >>= k') := by
  intro st hst
  obtain ⟨st1, h1, e1⟩ := hm st hst
  cases r with
  | error e =>
    refine ⟨st1, h1, ?_⟩
    simp only [StateT.run_bind, e1, Except.map]
    rfl
  | ok a =>
    obtain ⟨st2, h2, e2⟩ := hk a rfl st1 h1
    refine ⟨st2, h2, ?_⟩
    simp only [StateT.run_bind, e1, Except.map]
    exact e2

theorem liftE' (x : Except String α) : Sim Inv (liftE x) x := by
  intro st h
  refine ⟨st, h, ?_⟩
  cases x <;> rfl

theorem congr {m m' : CmpM α} {r r' : Except String α} (h : Sim Inv m r) (hm : m = m')
    (hr : r = r') : Sim Inv m' r' := hm ▸ hr ▸ h

end Sim

theorem Sim.cmpM {Inv : CmpState → Prop} {m₁ m₂ : CmpM SOrder} {r₁ r₂ : Except String SOrder}
    (h₁ : Sim Inv m₁ r₁) (h₂ : Sim Inv m₂ r₂) :
    Sim Inv (SOrder.cmpM m₁ m₂) (SOrder.cmpM r₁ r₂) := by
  unfold SOrder.cmpM
  refine Sim.bind h₁ fun a _ => ?_
  obtain ⟨s, o⟩ := a
  cases s <;> cases o <;> simp only
  all_goals first
    | exact Sim.pure' _
    | exact h₂
    | exact Sim.bind h₂ fun _ _ => Sim.pure' _

theorem Sim.zipM {Inv : CmpState → Prop} {β : Type} {f : β → β → CmpM SOrder}
    {g : β → β → Except String SOrder} (xs ys : List β)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, Sim Inv (f x y) (g x y)) :
    Sim Inv (SOrder.zipM f xs ys) (SOrder.zipM g xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact Sim.pure' _
  | cons x xs ih =>
    cases ys with
    | nil => exact Sim.pure' _
    | cons y ys =>
      simp only [SOrder.zipM]
      refine Sim.bind (h x (by simp) y (by simp)) fun a _ => ?_
      obtain ⟨s, o⟩ := a
      cases o <;> simp only
      all_goals first
        | exact Sim.pure' _
        | exact Sim.cmpM (Sim.pure' _) (ih ys fun x hx y hy =>
            h x (by simp [hx]) y (by simp [hy]))

/-! ## Reading and writing the cache -/

theorem cacheGet_run (flip b : Bool) (x y : Name) (st : CmpState) :
    (cacheGet flip b x y).run st =
      match st.cache[cacheKey b x y]? with
      | none => .ok (none, st)
      | some (o, left) =>
        if (left == x || o == .eq) = true then .ok (some o, st)
        else .ok (some (if flip then o.swap else o), { st with hazards := st.hazards + 1 }) := by
  cases h : st.cache[cacheKey b x y]? with
  | none =>
    simp [cacheGet, StateT.run_bind, Std.HashMap.get?_eq_getElem?, h]; rfl
  | some v =>
    obtain ⟨o, left⟩ := v
    simp [cacheGet, StateT.run_bind, Std.HashMap.get?_eq_getElem?, h]
    split <;> simp <;> rfl

theorem cachePut_run (b : Bool) (x y : Name) (o : SOrder) (st : CmpState) :
    (cachePut b x y o).run st =
      if o.strong then .ok ((), { st with cache := st.cache.insert (cacheKey b x y) (o.ord, x) })
      else .ok ((), st) := by
  unfold cachePut
  split <;> rfl

section cache

variable {A : Run} {ms : List MutConst} (hinj : NameInj ms) (hA : AddrCongr A.addr?)
include hinj hA

/-- Reading a coherent cache: a hit is the pure comparison of the queried pair, in the
query's orientation (the read flips a value stored for the swapped pair: `portFixes`). -/
theorem cacheGet_spec {st : CmpState} (hst : Coh A ms st) {e₁ e₂ : Ent} (h₁ : e₁ ∈ ents ms)
    (h₂ : e₂ ∈ ents ms) (b : Bool) :
    ∃ res st', (cacheGet true b e₁.name e₂.name).run st = .ok (res, st') ∧
      st'.cache = st.cache ∧
      ∀ o, res = some o → ∀ c, A.Adm b c → entP c e₁ e₂ = .ok ⟨true, o⟩ := by
  rw [cacheGet_run]
  cases hk : st.cache[cacheKey b e₁.name e₂.name]? with
  | none => exact ⟨none, st, rfl, rfl, by simp⟩
  | some v =>
    obtain ⟨o, left⟩ := v
    obtain ⟨f₁, hf₁, f₂, hf₂, hl, hkey, hent⟩ := hst _ _ hk
    simp only [cacheKey_fst] at hkey hent
    have same : ∀ {u v : Ent}, u ∈ ents ms → v ∈ ents ms → (u.name == v.name) = true → u = v :=
      fun hu hv h => hinj _ hu _ hv h
    simp only
    split
    · rename_i hif
      refine ⟨_, _, rfl, rfl, ?_⟩
      intro o' ho c hc
      cases ho
      rcases cacheKey_beq hkey with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · rw [same h₁ hf₁ k1, same h₂ hf₂ k2]; exact hent c hc
      · have e1 := same h₁ hf₂ k1
        have e2 := same h₂ hf₁ k2
        simp only [Bool.or_eq_true, beq_iff_eq] at hif
        rcases hif with hif | hif
        · -- `left` names `e₁` and `f₁ = e₂`: the pair is `(e₁, e₁)`
          have h12 : e₁ = e₂ :=
            same h₁ h₂ (BEq.trans (BEq.symm hif) (by rw [← e2] at hl; exact hl))
          have := hent c hc
          rw [← e2, ← e1, ← h12] at this
          rw [← h12]; exact this
        · subst hif
          have := entP_swap (hc.addr hA) (hent c hc)
          rw [e1, e2]; simpa using this
    · rename_i hif
      refine ⟨_, _, rfl, rfl, ?_⟩
      intro o' ho c hc
      cases ho
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hif
      rcases cacheKey_beq hkey with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exact absurd (by rw [same h₁ hf₁ k1]; exact hl) hif.1
      · have e1 := same h₁ hf₂ k1
        have e2 := same h₂ hf₁ k2
        have := entP_swap (hc.addr hA) (hent c hc)
        rw [e1, e2]
        simpa using this

omit hinj hA in
/-- Writing a true result keeps the cache coherent. -/
theorem cachePut_coh {st : CmpState} (hst : Coh A ms st) {e₁ e₂ : Ent} (h₁ : e₁ ∈ ents ms)
    (h₂ : e₂ ∈ ents ms) {b : Bool} {c : CmpCtx} (hc : A.Adm b c) {so : SOrder}
    (hso : entP c e₁ e₂ = .ok so) :
    ∃ st', (cachePut b e₁.name e₂.name so).run st = .ok ((), st') ∧ Coh A ms st' := by
  rw [cachePut_run]
  split
  · rename_i hs
    refine ⟨_, rfl, ?_⟩
    intro k v hkv
    simp only at hkv
    rw [Std.HashMap.getElem?_insert] at hkv
    split at hkv
    · rename_i hK
      cases hkv
      have hk1 : k.1 = b := by
        have := ((prod_beq_iff _ _).1 hK).1
        rw [cacheKey_fst] at this
        exact (beq_iff_eq.1 this).symm
      refine ⟨e₁, h₁, e₂, h₂, BEq.rfl, ?_, ?_⟩
      · rw [hk1]; exact BEq.symm hK
      · intro c' hc'
        rw [hk1] at hc'
        obtain ⟨s, o⟩ := so
        simp only at hs; subst hs
        exact entP_strong (hc.sameDom hc') hso
    · exact hst k v hkv
  · exact ⟨st, rfl, hst⟩

/-! ## The cached comparisons are the pure ones -/

omit hinj hA in
theorem liftE_run {α : Type} (x : Except String α) (st : CmpState) :
    (liftE x).run st = x.map (·, st) := by
  cases x <;> rfl

/-- The shape of `compareCtor` and `compareConstIn`: look up the pair, else compute, store
and return. With a coherent cache it returns the pure comparison. -/
theorem cached_sim {α : Type} {e₁ e₂ : Ent} (he₁ : e₁ ∈ ents ms) (he₂ : e₂ ∈ ents ms)
    {c : CmpCtx} (hc : A.Adm (c.mode == .blind) c) {body : CmpM SOrder}
    (hbody : Sim (Coh A ms) body (entP c e₁ e₂)) (ret : SOrder → α)
    (k : Option Ordering → CmpM α) (hsome : ∀ o, k (some o) = pure (ret ⟨true, o⟩))
    (hnone : k none = (do
      let so ← body
      cachePut (c.mode == .blind) e₁.name e₂.name so
      pure (ret so))) :
    Sim (Coh A ms) (cacheGet true (c.mode == .blind) e₁.name e₂.name >>= k)
      ((entP c e₁ e₂).map ret) := by
  intro st hst
  obtain ⟨res, st1, e1, hc1, hres⟩ := cacheGet_spec hinj hA hst he₁ he₂ (c.mode == .blind)
  have hst1 : Coh A ms st1 := fun k v h => hst k v (by rw [← hc1]; exact h)
  rw [StateT.run_bind, e1]
  simp only [bind, Except.bind]
  cases res with
  | some o =>
    refine ⟨st1, hst1, ?_⟩
    rw [hres o rfl c hc, hsome]
    rfl
  | none =>
    obtain ⟨st2, hst2, e2⟩ := hbody st1 hst1
    rw [hnone, StateT.run_bind, e2]
    cases hp : entP c e₁ e₂ with
    | error e => exact ⟨st2, hst2, rfl⟩
    | ok so =>
      obtain ⟨st3, e3, hst3⟩ := cachePut_coh hst2 he₁ he₂ hc hp
      refine ⟨st3, hst3, ?_⟩
      show (cachePut (c.mode == ExtMode.blind) e₁.name e₂.name so >>= fun _ => pure (ret so)).run st2 =
        Except.ok (ret so, st3)
      rw [StateT.run_bind, e3]
      rfl

theorem compareCtor_sim {c : CmpCtx} (hc : A.Adm (c.mode == .blind) c) {mx my : MutConst}
    (hmx : mx ∈ ms) (hmy : my ∈ ms) {x y : ConstructorVal} (hx : x ∈ mx.ctors)
    (hy : y ∈ my.ctors) :
    Sim (Coh A ms) (compareCtor true c mx.levelParams.toList my.levelParams.toList x y)
      (ctorP c mx.levelParams.toList my.levelParams.toList x y) := by
  have := cached_sim hinj hA (mem_ents_ctor hmx hx) (mem_ents_ctor hmy hy) hc
    (body := liftE (ctorP c mx.levelParams.toList my.levelParams.toList x y))
    (Sim.liftE' _) id (fun d => match d with
      | some o => pure ⟨true, o⟩
      | _ => do
        let so ← liftE (ctorP c mx.levelParams.toList my.levelParams.toList x y)
        cachePut (c.mode == .blind) x.cnst.name y.cnst.name so
        return so) (fun _ => rfl) rfl
  simp only [Ent.name, entP, Except.map_id] at this
  exact this

theorem compareInd_sim {c : CmpCtx} (hc : A.Adm (c.mode == .blind) c) {x y : Ind}
    (hx : MutConst.indc x ∈ ms) (hy : MutConst.indc y ∈ ms) :
    Sim (Coh A ms) (compareInd true c x y) (indP c x y) := by
  have hZ : Sim (Coh A ms)
      (compareCtors true c x.levelParams.toList y.levelParams.toList x.ctors.toList y.ctors.toList)
      (zipCtx (ctorC c) (x.levelParams.toList, x.ctors.toList)
        (y.levelParams.toList, y.ctors.toList)) :=
    Sim.zipM _ _ fun u hu v hv =>
      compareCtor_sim hinj hA hc (mx := .indc x) (my := .indc y) hx hy
        (by simpa [MutConst.ctors] using hu) (by simpa [MutConst.ctors] using hv)
  have hh := indHdr_eq x y
  unfold indHdr at hh
  unfold compareInd indP
  simp only [indHdr, hh]
  cases (compare x.levelParams.size y.levelParams.size).then
      ((compare x.numParams y.numParams).then
        ((compare x.numIndices y.numIndices).then (compare x.ctors.size y.ctors.size))) with
  | lt => exact Sim.pure' _
  | gt => exact Sim.pure' _
  | eq =>
    show Sim _ (do
        let ty ← liftE (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
        if (SOrder.cmp ⟨true, .eq⟩ ty).ord != .eq then pure (SOrder.cmp ⟨true, .eq⟩ ty) else do
          let cs ← compareCtors true c x.levelParams.toList y.levelParams.toList x.ctors.toList
            y.ctors.toList
          pure (SOrder.cmp (SOrder.cmp ⟨true, .eq⟩ ty) cs))
      (SOrder.cmpM (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
        (zipCtx (ctorC c) (x.levelParams.toList, x.ctors.toList)
          (y.levelParams.toList, y.ctors.toList)))
    unfold SOrder.cmpM
    refine Sim.bind (Sim.liftE' _) fun ty _ => ?_
    obtain ⟨s, o⟩ := ty
    cases s <;> cases o <;> simp only [SOrder.cmp, bne_iff_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, ↓reduceIte, not_true_eq_false]
    all_goals first
      | exact Sim.pure' _
      | exact Sim.congr (Sim.bind hZ fun _ _ => Sim.pure' _) rfl (by simp)

theorem compareConstBody_sim {c : CmpCtx} (hc : A.Adm (c.mode == .blind) c) {x y : MutConst}
    (hx : x ∈ ms) (hy : y ∈ ms) :
    Sim (Coh A ms) (compareConstBody true true c x y) (constP c x y) := by
  cases x <;> cases y <;> simp only [compareConstBody, constP]
  all_goals first
    | exact Sim.liftE' _
    | exact Sim.pure' _
    | exact compareInd_sim hinj hA hc hx hy

theorem compareConstIn_sim {c : CmpCtx} (hc : A.Adm (c.mode == .blind) c) {x y : MutConst}
    (hx : x ∈ ms) (hy : y ∈ ms) :
    Sim (Coh A ms) (compareConstIn true c x y) ((constP c x y).map (·.ord)) := by
  have := cached_sim hinj hA (mem_ents_mem hx) (mem_ents_mem hy) hc
    (compareConstBody_sim hinj hA hc hx hy) SOrder.ord (fun d => match d with
      | some o => pure o
      | _ => do
        let so ← compareConstBody true true c x y
        cachePut (c.mode == .blind) x.name y.name so
        return so.ord) (fun _ => rfl) rfl
  simp only [Ent.name, entP] at this
  exact this

end cache

/-! ## The comparison a rule set sorts by -/

/-- The context `compareConst` builds. -/
def ctxOf (rules : Rules) (addr? : Name → Option Address) (mode : ExtMode) (ctx : MutCtx) :
    CmpCtx :=
  { levels := rules.levels, mode, addr?, mutCtx := ctx }

/-- `compareConst` without the cache: the tie-break of the rule set over `constP`. -/
def constOrd (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx) (x y : MutConst) :
    Except String Ordering :=
  match rules.tieBreak with
  | .inline => (constP (ctxOf rules addr? .addr ctx) x y).map (·.ord)
  | .blind => (constP (ctxOf rules addr? .blind ctx) x y).map (·.ord)
  | .byAddress => do
    let b ← (constP (ctxOf rules addr? .blind ctx) x y).map (·.ord)
    if b != .eq then return b
    (constP (ctxOf rules addr? .addr ctx) x y).map (·.ord)

theorem Run.adm_ctxOf {A : Run} {ctx : MutCtx} (hdom : ∀ n, (ctx[n]?).isSome = A.dom n)
    (m : ExtMode) : A.Adm (m == .blind) (ctxOf A.rules A.addr? m ctx) := by
  refine ⟨rfl, rfl, ?_, hdom⟩
  cases m <;> rfl

theorem compareConst_sim {A : Run} {ms : List MutConst} (hinj : NameInj ms)
    (hA : AddrCongr A.addr?) (hpf : A.rules.portFixes = true) {ctx : MutCtx}
    (hdom : ∀ n, (ctx[n]?).isSome = A.dom n) {x y : MutConst} (hx : x ∈ ms) (hy : y ∈ ms) :
    Sim (Coh A ms) (compareConst A.rules A.addr? ctx x y) (constOrd A.rules A.addr? ctx x y) := by
  have hI := fun m => compareConstIn_sim hinj hA (A.adm_ctxOf hdom m) hx hy
  unfold compareConst constOrd
  rw [hpf]
  cases A.rules.tieBreak with
  | inline => exact hI .addr
  | blind => exact hI .blind
  | byAddress =>
    refine Sim.bind (hI .blind) fun b _ => ?_
    by_cases hb : b = .eq
    · subst hb
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine Sim.congr
        (r := (constP (ctxOf A.rules A.addr? .addr ctx) x y).map (·.ord) >>= pure)
        (Sim.bind (hI .addr) fun a _ => ?_) rfl (by simp)
      intro st hst
      by_cases ha : a = .eq
      · subst ha; exact ⟨st, hst, rfl⟩
      · simp only [bne_iff_ne, ne_eq, ha, not_false_eq_true, ↓reduceIte]
        exact ⟨{ st with addrDecided := st.addrDecided + 1 }, hst, rfl⟩
    · simp only [bne_iff_ne, ne_eq, hb, not_false_eq_true, ↓reduceIte]
      exact Sim.pure' _

/-- **The comparison of the code is the pure comparison** (`portFixes := true`): a comparison
from the empty cache returns `constOrd`. -/
theorem compareFresh_eq {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) (ctx : MutCtx) {ms : List MutConst}
    (hinj : NameInj ms) {x y : MutConst} (hx : x ∈ ms) (hy : y ∈ ms) :
    compareFresh rules addr? ctx x y = constOrd rules addr? ctx x y := by
  let A : Run := ⟨rules, addr?, fun n => (ctx[n]?).isSome⟩
  obtain ⟨st', -, e⟩ := compareConst_sim (A := A) hinj hA hpf (fun _ => rfl) hx hy {}
    (coh_empty A ms)
  unfold compareFresh
  simp only [A] at e
  rw [e]
  cases constOrd rules addr? ctx x y <;> rfl

/-! ## The comparison of the code is a total preorder at a fixed context -/

/-- An `Ordering` result read as a strong comparison. -/
def liftOrd (r : Except String Ordering) : Except String SOrder := r.map (⟨true, ·⟩)

theorem PreOn.ord {α : Type} {S : α → Prop} {F : α → α → Except String SOrder} (h : PreOn S F) :
    PreOn S (fun a b => liftOrd ((F a b).map (·.ord))) where
  swap {a b} ha hb := by
    intro s o e
    cases hf : F a b with
    | error err => rw [hf] at e; cases e
    | ok r =>
      rw [hf] at e
      simp only [liftOrd, Except.map, Except.ok.injEq, SOrder.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [h.swap ha hb hf]; rfl
  trans {a b c} ha hb hc := by
    rintro ⟨s1, o1, e1, n1⟩ ⟨s2, o2, e2, n2⟩
    cases f1 : F a b with
    | error err => rw [f1] at e1; cases e1
    | ok r1 =>
      cases f2 : F b c with
      | error err => rw [f2] at e2; cases e2
      | ok r2 =>
        rw [f1] at e1; rw [f2] at e2
        simp only [liftOrd, Except.map, Except.ok.injEq, SOrder.mk.injEq] at e1 e2
        obtain ⟨-, rfl⟩ := e1; obtain ⟨-, rfl⟩ := e2
        obtain ⟨s3, o3, e3, n3⟩ := h.trans ha hb hc ⟨_, _, f1, n1⟩ ⟨_, _, f2, n2⟩
        exact ⟨true, o3, by rw [e3]; rfl, n3⟩

theorem liftOrd_lex (B A : Except String Ordering) :
    liftOrd (B >>= fun b => if b != .eq then pure b else A) = lexIf (liftOrd B) (liftOrd A) := by
  cases B with
  | error e => rfl
  | ok b => cases b <;> rfl

theorem constOrd_total (rules : Rules) {addr? : Name → Option Address} (hA : AddrCongr addr?)
    (ctx : MutCtx) : TotalPre (fun x y => liftOrd (constOrd rules addr? ctx x y)) := by
  have P := fun m => (constP_total (ctxOf rules addr? m ctx) hA).ord
  unfold constOrd
  cases rules.tieBreak with
  | inline => exact P .addr
  | blind => exact P .blind
  | byAddress =>
    refine ((P .blind).lexIf (P .addr)).congr fun x y _ _ => ?_
    exact (liftOrd_lex _ _).symm

/-- **The comparator is a total preorder at a fixed context** (design document §3.2, §3.5
(i)), for the comparison the code runs: `compareFresh` (one comparison from the empty
cache) under any rule set with `portFixes := true`, at any class context, on the members of
a component whose names identify their members and constructors. -/
theorem compareFresh_total {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) (ctx : MutCtx) {ms : List MutConst}
    (hinj : NameInj ms) :
    PreOn (· ∈ ms) (fun x y => liftOrd (compareFresh rules addr? ctx x y)) :=
  ((constOrd_total rules hA ctx).mono fun _ _ => trivial).congr fun x y hx hy => by
    rw [compareFresh_eq hpf hA ctx hinj hx hy]

/-! ## Defect C2 of the Lean port (`portFixes := false`) -/

theorem cacheKey_comm (b : Bool) (x y : Name) : (cacheKey b x y == cacheKey b y x) = true := by
  have hs : Ix.nameCompare y x = (Ix.nameCompare x y).swap :=
    Std.OrientedCmp.eq_swap (cmp := Ix.nameCompare)
  unfold cacheKey
  change ((match Ix.nameCompare x y with | .lt => (b, x, y) | _ => (b, y, x)) ==
    (match Ix.nameCompare y x with | .lt => (b, y, x) | _ => (b, x, y))) = true
  rw [hs]
  cases h : Ix.nameCompare x y <;> simp only [Ordering.swap, prod_beq_iff]
  · exact ⟨BEq.rfl, BEq.rfl, BEq.rfl⟩
  · have := nameCompare_eq_iff.1 h
    exact ⟨BEq.rfl, BEq.symm this, this⟩
  · exact ⟨BEq.rfl, BEq.rfl, BEq.rfl⟩

/-- Defect C2 of the design document §3.4, as it stands under `Rules.today`
(`portFixes := false`): a strong `lt` stored for `(x, y)` is read back as `lt` for the
swapped query `(y, x)`; with the port fix (`flip := true`) it is read back as `gt`. -/
theorem cacheGet_today_reversed (b : Bool) (x y : Name) (hxy : (x == y) = false) :
    let st : CmpState := { cache := ({} : Std.HashMap _ _).insert (cacheKey b x y) (.lt, x) }
    (cacheGet false b y x).run st = .ok (some .lt, { st with hazards := st.hazards + 1 }) ∧
    (cacheGet true b y x).run st = .ok (some .gt, { st with hazards := st.hazards + 1 }) := by
  intro st
  have hk : st.cache[cacheKey b y x]? = some (.lt, x) := by
    simp only [st, Std.HashMap.getElem?_insert, cacheKey_comm b x y, ↓reduceIte]
  refine ⟨?_, ?_⟩ <;> rw [cacheGet_run, hk] <;> simp [hxy]

end Ix.CompileCert.Canon
