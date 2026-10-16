import Ix.CompileCert.Canon.Rel

/-! # Pass 1's strong-result cache returns the comparator's own results

CS-01, ported from the donor `a9cf3607` (`Canon/Cache`). `compareConst`
(and through it `compareInd`, `compareCtor`) runs in `CmpM`: a state whose
cache maps the unordered name pair to an ordering and the name that was on
the left when it was computed; a hit is read back in the call's
orientation. Since the CQ2.25 follow-up the keys are exact
(`ExactName × ExactName`, ordered by `nameCompareExact`) and the
orientation test is `nameEq`. Caching strong results across the rounds of
one refinement is sound:

* `Coh A ms st`: every cache entry is the true strong result of two entries
  (members, or constructors with their inductives' level lists) of the
  component `ms`, under every context of the run `A` (same address map and
  in-block names; any class indices);
* the cached comparisons return exactly the pure ones and keep `Coh`
  (`compareCtor_sim` … `compareConst_sim`), given `NameInj ms` (the
  component's member and constructor names identify their entries, as
  Lean's names do);
* the pure comparison a round sorts by, `constOrd`, is a total preorder
  (`constOrd_total`).

Adapted to today's Pass 1: one external mode (by address), one tie-break,
the cache read in the call's orientation (the donor's port fix C2 is the
only behaviour now), `CmpError`. -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Level Expr MutConst Def Ind Rec ConstructorVal RecursorVal RecursorRule MutCtx)

/-! ## Cache keys -/

/-- Two equal cache keys name the same unordered pair. -/
theorem cacheKey_eq {x y x' y' : Name} (h : cacheKey x y = cacheKey x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  unfold cacheKey at h
  split at h <;> split at h <;> injection h with h1 h2
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨h1, h2⟩
  · exact .inr ⟨h2, h1⟩
  · exact .inl ⟨h2, h1⟩

/-! ## The component's entries -/

/-- An entry of a component's name table: a member, or a constructor of a
member. -/
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

/-- The component's member and constructor names identify their entries
(Lean's names are unique). -/
def NameInj (ms : List MutConst) : Prop :=
  ∀ e₁ ∈ ents ms, ∀ e₂ ∈ ents ms, e₁.name = e₂.name → e₁ = e₂

/-- The pure comparison of two entries. -/
def entP (c : CmpCtx) : Ent → Ent → Except CmpError SOrder
  | .mem x, .mem y => constP c x y
  | .ctor mx x, .ctor my y => compareCtorKeys c mx.levelParams.toList my.levelParams.toList x y
  | _, _ => .error (.refinement "entP: kinds")

theorem entP_swap {c : CmpCtx} {e₁ e₂ : Ent} {s o} (h : entP c e₁ e₂ = .ok ⟨s, o⟩) :
    entP c e₂ e₁ = .ok ⟨s, o.swap⟩ := by
  cases e₁ <;> cases e₂ <;> simp only [entP] at h ⊢
  · exact (constP_total c).swap trivial trivial h
  · cases h
  · cases h
  · exact (ctorP_total c).swap (a := (_, _)) (b := (_, _)) trivial trivial h


theorem entP_strong {c c' : CmpCtx} (hd : SameDom c c') {e₁ e₂ : Ent} {o}
    (h : entP c e₁ e₂ = .ok ⟨true, o⟩) : entP c' e₁ e₂ = .ok ⟨true, o⟩ := by
  cases e₁ <;> cases e₂ <;> simp only [entP] at h ⊢
  · exact constP_strong hd _ _ _ h
  · cases h
  · cases h
  · exact ctorP_strong hd _ _ _ _ _ h

/-! ## Runs and coherent caches -/

/-- What every round of one refinement shares: the address map and the
names in the block. -/
structure Run where
  addr? : Name → Option Address
  dom : Name → Prop

/-- A context of the run. -/
def Run.Adm (A : Run) (c : CmpCtx) : Prop :=
  c.addr? = A.addr? ∧ ∀ n, (c.mutCtx[n]?).isSome = true ↔ A.dom n

theorem Run.Adm.sameDom {A : Run} {c c' : CmpCtx} (h : A.Adm c) (h' : A.Adm c') : SameDom c c' where
  addr := h.1.trans h'.1.symm
  dom n := Bool.eq_iff_iff.2 ((h.2 n).trans (h'.2 n).symm)

/-- Every cache entry is a true strong result of two entries of the
component under every context of the run. -/
def Coh (A : Run) (ms : List MutConst) (st : CmpState) : Prop :=
  ∀ (k : Ix.Compile.ExactKey.ExactName × Ix.Compile.ExactKey.ExactName) (v : Ordering × Name),
    st.cache[k]? = some v →
      ∃ e₁ ∈ ents ms, ∃ e₂ ∈ ents ms, v.2 = e₁.name ∧
        k = cacheKey e₁.name e₂.name ∧
        ∀ c, A.Adm c → entP c e₁ e₂ = .ok ⟨true, v.1⟩

theorem coh_empty (A : Run) (ms : List MutConst) : Coh A ms {} := by
  intro k v h
  simp at h

/-! ## Simulation of a cached computation by a pure one -/

/-- `m`, run from any state satisfying `Inv`, returns what `r` returns and
ends in a state satisfying `Inv`. -/
def Sim (Inv : CmpState → Prop) {α : Type} (m : CmpM α) (r : Except CmpError α) : Prop :=
  ∀ st, Inv st → ∃ st', Inv st' ∧ m.run st = r.map (fun a => (a, st'))

namespace Sim

variable {Inv : CmpState → Prop} {α β : Type}

theorem pure' (a : α) : Sim Inv (pure a) (pure a) := fun st h => ⟨st, h, rfl⟩

theorem bind {m : CmpM α} {r : Except CmpError α} {k : α → CmpM β} {k' : α → Except CmpError β}
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

theorem liftE' (x : Except CmpError α) : Sim Inv (liftE x) x := by
  intro st h
  refine ⟨st, h, ?_⟩
  cases x <;> rfl

theorem congr {m m' : CmpM α} {r r' : Except CmpError α} (h : Sim Inv m r) (hm : m = m')
    (hr : r = r') : Sim Inv m' r' := hm ▸ hr ▸ h

end Sim

theorem Sim.cmpM {Inv : CmpState → Prop} {m₁ m₂ : CmpM SOrder} {r₁ r₂ : Except CmpError SOrder}
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
    {g : β → β → Except CmpError SOrder} (xs ys : List β)
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

theorem cacheGet_run (x y : Name) (st : CmpState) :
    (cacheGet x y).run st =
      match st.cache[cacheKey x y]? with
      | none => .ok (none, st)
      | some (o, left) =>
        .ok (some (if Ix.Compile.ExactKey.nameEq left x = true then o else o.swap), st) := by
  cases h : st.cache[cacheKey x y]? with
  | none =>
    simp [cacheGet, StateT.run_bind, Std.HashMap.get?_eq_getElem?, h]; rfl
  | some v =>
    obtain ⟨o, left⟩ := v
    simp [cacheGet, StateT.run_bind, Std.HashMap.get?_eq_getElem?, h]; rfl

theorem cachePut_run (x y : Name) (o : SOrder) (st : CmpState) :
    (cachePut x y o).run st =
      if o.strong then .ok ((), { st with cache := st.cache.insert (cacheKey x y) (o.ord, x) })
      else .ok ((), st) := by
  unfold cachePut
  split <;> rfl

section cache

variable {A : Run} {ms : List MutConst} (hinj : NameInj ms)
include hinj

/-- Reading a coherent cache: a hit is the pure comparison of the queried
pair, in the query's orientation. -/
theorem cacheGet_spec {st : CmpState} (hst : Coh A ms st) {e₁ e₂ : Ent} (h₁ : e₁ ∈ ents ms)
    (h₂ : e₂ ∈ ents ms) :
    ∃ res, (cacheGet e₁.name e₂.name).run st = .ok (res, st) ∧
      ∀ o, res = some o → ∀ c, A.Adm c → entP c e₁ e₂ = .ok ⟨true, o⟩ := by
  rw [cacheGet_run]
  cases hk : st.cache[cacheKey e₁.name e₂.name]? with
  | none => exact ⟨none, rfl, by simp⟩
  | some v =>
    obtain ⟨o, left⟩ := v
    obtain ⟨f₁, hf₁, f₂, hf₂, hl, hkey, hent⟩ := hst _ _ hk
    simp only at hl
    have same : ∀ {u v : Ent}, u ∈ ents ms → v ∈ ents ms → u.name = v.name → u = v :=
      fun hu hv h => hinj _ hu _ hv h
    refine ⟨_, rfl, ?_⟩
    intro o' ho c hc
    cases ho
    rcases cacheKey_eq hkey with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · -- the stored pair is the queried pair
      have e1 := same h₁ hf₁ k1
      have e2 := same h₂ hf₂ k2
      subst e1; subst e2
      simp only [nameEq_true hl, ↓reduceIte]
      exact hent c hc
    · -- the stored pair is the swapped pair
      have e1 := same h₁ hf₂ k1
      have e2 := same h₂ hf₁ k2
      subst e1; subst e2
      by_cases hlx : left = e₁.name
      · -- `left` names `e₁` and `e₂`: the pair is `(e₁, e₁)`
        have h12 : e₁ = e₂ := same h₁ h₂ (hlx.symm.trans hl)
        subst h12
        simp only [nameEq_true hlx, ↓reduceIte]
        exact hent c hc
      · simp only [nameEq_false hlx, Bool.false_eq_true, ↓reduceIte]
        have := entP_swap (hent c hc)
        simpa using this

omit hinj in
/-- Writing a true result keeps the cache coherent. -/
theorem cachePut_coh {st : CmpState} (hst : Coh A ms st) {e₁ e₂ : Ent} (h₁ : e₁ ∈ ents ms)
    (h₂ : e₂ ∈ ents ms) {c : CmpCtx} (hc : A.Adm c) {so : SOrder}
    (hso : entP c e₁ e₂ = .ok so) :
    ∃ st', (cachePut e₁.name e₂.name so).run st = .ok ((), st') ∧ Coh A ms st' := by
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
      refine ⟨e₁, h₁, e₂, h₂, rfl, (beq_iff_eq.1 hK).symm, ?_⟩
      intro c' hc'
      obtain ⟨s, o⟩ := so
      simp only at hs; subst hs
      exact entP_strong (hc.sameDom hc') hso
    · exact hst k v hkv
  · exact ⟨st, rfl, hst⟩

/-! ## The cached comparisons are the pure ones -/

omit hinj in
theorem liftE_run {α : Type} (x : Except CmpError α) (st : CmpState) :
    (liftE x).run st = x.map (·, st) := by
  cases x <;> rfl

/-- The shape of `compareCtor` and `compareConst`: look up the pair, else
compute, store and return. With a coherent cache it returns the pure
comparison. -/
theorem cached_sim {α : Type} {e₁ e₂ : Ent} (he₁ : e₁ ∈ ents ms) (he₂ : e₂ ∈ ents ms)
    {c : CmpCtx} (hc : A.Adm c) {body : CmpM SOrder}
    (hbody : Sim (Coh A ms) body (entP c e₁ e₂)) (ret : SOrder → α)
    (k : Option Ordering → CmpM α) (hsome : ∀ o, k (some o) = pure (ret ⟨true, o⟩))
    (hnone : k none = (do
      let so ← body
      cachePut e₁.name e₂.name so
      pure (ret so))) :
    Sim (Coh A ms) (cacheGet e₁.name e₂.name >>= k) ((entP c e₁ e₂).map ret) := by
  intro st hst
  obtain ⟨res, e1, hres⟩ := cacheGet_spec hinj hst he₁ he₂
  rw [StateT.run_bind, e1]
  simp only [bind, Except.bind]
  cases res with
  | some o =>
    refine ⟨st, hst, ?_⟩
    rw [hres o rfl c hc, hsome]
    rfl
  | none =>
    obtain ⟨st2, hst2, e2⟩ := hbody st hst
    rw [hnone, StateT.run_bind, e2]
    cases hp : entP c e₁ e₂ with
    | error e => exact ⟨st2, hst2, rfl⟩
    | ok so =>
      obtain ⟨st3, e3, hst3⟩ := cachePut_coh hst2 he₁ he₂ hc hp
      refine ⟨st3, hst3, ?_⟩
      show (cachePut e₁.name e₂.name so >>= fun _ => pure (ret so)).run st2 = Except.ok (ret so, st3)
      rw [StateT.run_bind, e3]
      rfl

theorem compareCtor_sim {c : CmpCtx} (hc : A.Adm c) {mx my : MutConst}
    (hmx : mx ∈ ms) (hmy : my ∈ ms) {x y : ConstructorVal} (hx : x ∈ mx.ctors)
    (hy : y ∈ my.ctors) :
    Sim (Coh A ms) (compareCtor c mx.levelParams.toList my.levelParams.toList x y)
      (compareCtorKeys c mx.levelParams.toList my.levelParams.toList x y) := by
  have := cached_sim hinj (mem_ents_ctor hmx hx) (mem_ents_ctor hmy hy) hc
    (body := liftE (compareCtorKeys c mx.levelParams.toList my.levelParams.toList x y))
    (Sim.liftE' _) id (fun d => match d with
      | some o => pure ⟨true, o⟩
      | _ => do
        let so ← liftE (compareCtorKeys c mx.levelParams.toList my.levelParams.toList x y)
        cachePut x.cnst.name y.cnst.name so
        return so) (fun _ => rfl) rfl
  simp only [Ent.name, entP, Except.map_id] at this
  exact this

theorem compareInd_sim {c : CmpCtx} (hc : A.Adm c) {x y : Ind}
    (hx : MutConst.indc x ∈ ms) (hy : MutConst.indc y ∈ ms) :
    Sim (Coh A ms) (compareInd c x y) (indP c x y) := by
  have hZ : Sim (Coh A ms)
      (compareCtors c x.levelParams.toList y.levelParams.toList x.ctors.toList y.ctors.toList)
      (zipCtx (ctorC c) (x.levelParams.toList, x.ctors.toList)
        (y.levelParams.toList, y.ctors.toList)) :=
    Sim.zipM _ _ fun u hu v hv =>
      compareCtor_sim hinj hc (mx := .indc x) (my := .indc y) hx hy
        (by simpa [MutConst.ctors] using hu) (by simpa [MutConst.ctors] using hv)
  have hh := indHeader_eq x y
  unfold compareInd indP
  simp only [hh]
  cases (compare x.levelParams.size y.levelParams.size).then
      ((compare x.numParams y.numParams).then
        ((compare x.numIndices y.numIndices).then (compare x.ctors.size y.ctors.size))) with
  | lt => exact Sim.pure' _
  | gt => exact Sim.pure' _
  | eq =>
    show Sim _ (do
        let ty ← liftE (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
        if (SOrder.cmp ⟨true, .eq⟩ ty).ord != .eq then pure (SOrder.cmp ⟨true, .eq⟩ ty) else do
          let cs ← compareCtors c x.levelParams.toList y.levelParams.toList x.ctors.toList
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

theorem compareConstBody_sim {c : CmpCtx} (hc : A.Adm c) {x y : MutConst}
    (hx : x ∈ ms) (hy : y ∈ ms) :
    Sim (Coh A ms) (compareConstBody c x y) (constP c x y) := by
  cases x <;> cases y <;> simp only [compareConstBody, constP]
  all_goals first
    | exact Sim.liftE' _
    | exact Sim.pure' _
    | exact compareInd_sim hinj hc hx hy

/-- The context `compareConst` builds. -/
def ctxOf (addr? : Name → Option Address) (ctx : MutCtx) : CmpCtx := { addr?, mutCtx := ctx }

/-- `compareConst` without the cache. -/
def constOrd (addr? : Name → Option Address) (ctx : MutCtx) (x y : MutConst) :
    Except CmpError Ordering :=
  (constP (ctxOf addr? ctx) x y).map (·.ord)

omit hinj in
theorem Run.adm_ctxOf {A : Run} {ctx : MutCtx} (hdom : ∀ n, (ctx[n]?).isSome = true ↔ A.dom n) :
    A.Adm (ctxOf A.addr? ctx) :=
  ⟨rfl, hdom⟩

/-- **The comparison of the code is the pure comparison**, from a coherent
cache. -/
theorem compareConst_sim {ctx : MutCtx} (hdom : ∀ n, (ctx[n]?).isSome = true ↔ A.dom n)
    {x y : MutConst} (hx : x ∈ ms) (hy : y ∈ ms) :
    Sim (Coh A ms) (compareConst A.addr? ctx x y) (constOrd A.addr? ctx x y) := by
  have := cached_sim hinj (mem_ents_mem hx) (mem_ents_mem hy) (Run.adm_ctxOf hdom)
    (compareConstBody_sim hinj (Run.adm_ctxOf hdom) hx hy) SOrder.ord (fun d => match d with
      | some o => pure o
      | _ => do
        let so ← compareConstBody (ctxOf A.addr? ctx) x y
        cachePut x.name y.name so
        return so.ord) (fun _ => rfl) rfl
  simp only [Ent.name, entP] at this
  exact this

end cache

/-! ## The comparison a round sorts by is a total preorder -/

/-- An `Ordering` result read as a strong comparison. -/
def liftOrd (r : Except CmpError Ordering) : Except CmpError SOrder := r.map (⟨true, ·⟩)

theorem PreOn.ord {α : Type} {S : α → Prop} {F : α → α → Except CmpError SOrder} (h : PreOn S F) :
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

/-- **The comparator is a total preorder at a fixed context.** -/
theorem constOrd_total (addr? : Name → Option Address) (ctx : MutCtx) :
    TotalPre (fun x y => liftOrd (constOrd addr? ctx x y)) :=
  (constP_total (ctxOf addr? ctx)).ord

end Ix.CompileCert.Canon
