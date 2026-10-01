import Compilatrix.Xv.Select.Proof.Term

/-!
# Pending values of folded statements

A fold moves a statement `y := r` of a block into a later consumer, whose
instructions read `r`'s operands instead of `y`. In the Lir run, `y` holds
`r`'s value at the consumer: the stability check (`stableFrom`) keeps every
statement between them from redefining `y` or an operand of `r`, and a load
folds only with no store or call in between (`pureBetween`).

`PendInv c i ρ mem ctx`: at position `i` of the block, every assignment
`y := r` before `i` whose window up to `i` is stable (and, for a load,
pure) has its value in `y`. It holds at block entry (`PendInv.zero`), steps
with each statement (`PendInv.step`), survives a call for the values the
call's results do not overwrite (`PendInv.call`), and gives the pending
facts each rule needs at its site (`PendInv.pend`).
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.Xv.Select

/-! ## Block analyses -/

/-- One step of `defSites`. -/
def defStep (m : NatMap (Nat × Lir.Rhs)) (p : Lir.Stmt × Nat) : NatMap (Nat × Lir.Rhs) :=
  match p with
  | (.assign x r, i) => m.insert x (i, r)
  | _ => m

theorem defSites_eq (body : List Lir.Stmt) : defSites body = body.zipIdx.foldl defStep {} := by
  unfold defSites
  congr
  funext m p
  obtain ⟨s, i⟩ := p
  cases s <;> rfl

theorem foldl_defStep {body : List Lir.Stmt} :
    ∀ (L : List (Lir.Stmt × Nat)) (m : NatMap (Nat × Lir.Rhs)), (∀ p ∈ L, body[p.2]? = some p.1) →
      (∀ (y : VReg) j r, m[y]? = some (j, r) → body[j]? = some (.assign y r)) →
      ∀ (y : VReg) j r, (L.foldl defStep m)[y]? = some (j, r) → body[j]? = some (.assign y r)
  | [], m, _, hm, y, j, r, h => hm y j r h
  | (s, i) :: L, m, hL, hm, y, j, r, h => by
      rw [List.foldl_cons] at h
      refine foldl_defStep L _ (fun p hp => hL p (List.mem_cons_of_mem _ hp)) ?_ y j r h
      intro y' j' r' h'
      have hi : body[i]? = some s := hL (s, i) List.mem_cons_self
      cases s with
      | assign x r'' =>
        simp only [defStep] at h'
        by_cases hx : x = y'
        · subst hx
          rw [Std.TreeMap.getElem?_insert_self] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          exact hi
        · rw [Std.TreeMap.getElem?_insert] at h'
          simp [hx] at h'
          exact hm y' j' r' h'
      | store => exact hm y' j' r' h'
      | call => exact hm y' j' r' h'

/-- The statement a definition site names assigns that register. -/
theorem defSites_spec {body : List Lir.Stmt} {y : VReg} {j : Nat} {r : Lir.Rhs}
    (h : (defSites body)[y]? = some (j, r)) : body[j]? = some (.assign y r) := by
  rw [defSites_eq] at h
  exact foldl_defStep body.zipIdx {} (fun p hp => List.mk_mem_zipIdx_iff_getElem?.mp hp) (by simp) y j r h

theorem defSites_unique {body : List Lir.Stmt} {y y' : VReg} {j : Nat} {r r' : Lir.Rhs}
    (h : (defSites body)[y]? = some (j, r)) (h' : (defSites body)[y']? = some (j, r')) : y = y' ∧ r = r' := by
  have := (defSites_spec h).symm.trans (defSites_spec h')
  simp only [Option.some.injEq, Lir.Stmt.assign.injEq] at this
  exact this

/-- Whether a statement is a store or a call. -/
def Lir.Stmt.isEffect : Lir.Stmt → Bool
  | .store .. | .call .. => true
  | _ => false

theorem mem_effectSites {body : List Lir.Stmt} {i : Nat} {s : Lir.Stmt} (hs : body[i]? = some s)
    (he : Lir.Stmt.isEffect s = true) : i ∈ effectSites body := by
  unfold effectSites
  rw [List.mem_filterMap]
  refine ⟨(s, i), List.mk_mem_zipIdx_iff_getElem?.mpr hs, ?_⟩
  cases s <;> simp_all [Lir.Stmt.isEffect]

/-- The analyses of a block context. -/
structure BlockCtx (c : Ctx) : Prop where
  defs : c.defs = defSites c.body
  effects : c.effects = effectSites c.body

/-! ## Statements leave other registers and, but for stores, memory -/

theorem exec_other {s : Lir.Stmt} {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (h : s.exec ρ mem ctx = some (ρ', mem')) :
    (∀ u, u ∉ s.defs → ρ'[u]? = ρ[u]?) ∧ (Lir.Stmt.isEffect s = false → mem' = mem) := by
  cases s with
  | assign x r =>
    simp only [Lir.Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨v, -, rfl, rfl⟩ := h
    refine ⟨fun u hu => ?_, fun _ => rfl⟩
    simp only [Lir.Stmt.defs, List.mem_singleton] at hu
    exact insert_ne (Ne.symm hu)
  | store w m a =>
    simp only [Lir.Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun _ _ => rfl, fun h' => by simp [Lir.Stmt.isEffect] at h'⟩
    · cases h
  | call => simp [Lir.Stmt.exec] at h

theorem Arg.eval_congr {a : Lir.Arg} {ρ ρ' : Env} (h : ∀ u ∈ a.uses, ρ'[u]? = ρ[u]?) : a.eval ρ' = a.eval ρ := by
  cases a with
  | v x => exact h x (by simp [uses_v])
  | imm k => rfl

theorem Addr.eval_congr {m : Lir.Addr} {ρ ρ' : Env} {ctx : Word} (h : ∀ u ∈ m.uses, ρ'[u]? = ρ[u]?) :
    m.eval ρ' ctx = m.eval ρ ctx := by
  obtain ⟨base, index, disp⟩ := m
  rcases base with _ | (y | _) <;> rcases index with _ | ⟨z, s⟩ <;>
    simp only [Lir.Addr.eval] <;>
    (try rw [h y (by simp [Lir.Addr.uses, Lir.Base.uses])]) <;>
    (try rw [h z (by simp [Lir.Addr.uses, Lir.Base.uses])])

/-- A right-hand side's value depends only on its operands and, for a load,
memory. -/
theorem Rhs.eval_congr {r : Lir.Rhs} {ρ ρ' : Env} {mem mem' : X86.Memory} {ctx : Word}
    (h : ∀ u ∈ r.uses, ρ'[u]? = ρ[u]?) (hm : (∃ w e m, r = .load w e m) → mem' = mem) :
    r.eval ρ' mem' ctx = r.eval ρ mem ctx := by
  have hs : ∀ {a : Lir.Arg}, (∀ u ∈ a.uses, u ∈ r.uses) → a.eval ρ' = a.eval ρ :=
    fun ha => Arg.eval_congr fun u hu => h u (ha u hu)
  cases r with
  | arg a => exact hs (fun u hu => by simpa [Lir.Rhs.uses] using hu)
  | bin o w a b =>
    simp only [Lir.Rhs.eval]
    rw [hs (fun u hu => by simp [Lir.Rhs.uses, hu]), hs (fun u hu => by simp [Lir.Rhs.uses, hu])]
  | load w e m =>
    simp only [Lir.Rhs.eval]
    rw [Addr.eval_congr (fun u hu => h u (by simpa [Lir.Rhs.uses] using hu)), hm ⟨w, e, m, rfl⟩]
  | addr m => exact Addr.eval_congr fun u hu => h u (by simpa [Lir.Rhs.uses] using hu)
  | select c w a b t f =>
    simp only [Lir.Rhs.eval]
    rw [hs (fun u hu => by simp [Lir.Rhs.uses, hu]), hs (fun u hu => by simp [Lir.Rhs.uses, hu]),
      hs (fun u hu => by simp [Lir.Rhs.uses, hu]), hs (fun u hu => by simp [Lir.Rhs.uses, hu])]
  | test c w a b =>
    simp only [Lir.Rhs.eval]
    rw [hs (fun u hu => by simp [Lir.Rhs.uses, hu]), hs (fun u hu => by simp [Lir.Rhs.uses, hu])]


/-! ## Windows -/

theorem window_succ {body : List Lir.Stmt} {j i : Nat} {s : Lir.Stmt} (hj : j ≤ i) (hs : body[i]? = some s) :
    (body.drop j).take (i + 1 - j) = (body.drop j).take (i - j) ++ [s] := by
  rw [show i + 1 - j = (i - j) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show j + (i - j) = i by omega, hs]
  rfl

theorem window_ne_nil {body : List Lir.Stmt} {j i : Nat} (hj : j < i) (hlen : j < body.length) :
    (body.drop j).take (i - j) ≠ [] := by
  intro h
  rw [List.take_eq_nil_iff] at h
  rcases h with h | h
  · omega
  · rw [List.drop_eq_nil_iff] at h; omega

theorem stableFrom_snoc {y : VReg} {r : Lir.Rhs} {s : Lir.Stmt} :
    ∀ {L : List Lir.Stmt}, L ≠ [] → stableFrom y r (L ++ [s]) = true →
      stableFrom y r L = true ∧ (s.defs.all fun d => d != y && !r.uses.contains d) = true
  | [], h, _ => absurd rfl h
  | t :: rest, _, h => by
      simp only [List.cons_append, stableFrom, Bool.and_eq_true, List.all_append, List.all_cons, List.all_nil,
        Bool.and_true] at h ⊢
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem all_avoid {ds us : List VReg} {y : VReg} (h : (ds.all fun d => d != y && !us.contains d) = true) :
    ∀ d ∈ ds, d ≠ y ∧ d ∉ us := by
  intro d hd
  have h' := List.all_eq_true.1 h d hd
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h'
  refine ⟨h'.1, fun hu => ?_⟩
  have : us.contains d = true := List.contains_iff_mem.2 hu
  simp_all

theorem stableFrom_single {y : VReg} {r : Lir.Rhs} {s : Lir.Stmt} (h : stableFrom y r [s] = true) :
    ∀ d ∈ s.defs, d ∉ r.uses := by
  simp only [stableFrom, List.all_nil, Bool.and_true] at h
  intro d hd hu
  have h' := List.all_eq_true.1 h d hd
  have : r.uses.contains d = true := List.contains_iff_mem.2 hu
  simp_all

/-! ## Pending values -/

/-- At position `i` of the block, every stable assignment before `i` has its
value. -/
def PendInv (c : Ctx) (i : Nat) (ρ : Env) (mem : X86.Memory) (ctx : Word) : Prop :=
  ∀ (y : VReg) (j : Nat) (r : Lir.Rhs), c.defs[y]? = some (j, r) → j < i →
    stableFrom y r ((c.body.drop j).take (i - j)) = true →
    (∀ w e m, r = .load w e m → (c.effects.all fun p => p ≤ j || i ≤ p) = true) →
    ∃ v, ρ[y]? = some v ∧ r.eval ρ mem ctx = some v

theorem PendInv.zero (c : Ctx) (ρ : Env) (mem : X86.Memory) (ctx : Word) : PendInv c 0 ρ mem ctx :=
  fun _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)

theorem pure_succ {c : Ctx} {j i : Nat} (h : (c.effects.all fun p => p ≤ j || i + 1 ≤ p) = true) :
    (c.effects.all fun p => p ≤ j || i ≤ p) = true := by
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  intro p hp
  rcases h p hp with h | h
  · exact .inl h
  · exact .inr (by omega)

theorem pure_not_effect {c : Ctx} (hc : BlockCtx c) {j i : Nat} {s : Lir.Stmt} (hji : j < i) (hs : c.body[i]? = some s)
    (h : (c.effects.all fun p => p ≤ j || i + 1 ≤ p) = true) : Lir.Stmt.isEffect s = false := by
  cases he : Lir.Stmt.isEffect s with
  | false => rfl
  | true =>
    have hmem : i ∈ c.effects := by rw [hc.effects]; exact mem_effectSites hs he
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h i hmem with h | h <;> omega

/-- A statement other than a call keeps the stable values pending. -/
theorem PendInv.step {c : Ctx} (hc : BlockCtx c) {i : Nat} {s : Lir.Stmt} {ρ ρ' : Env} {mem mem' : X86.Memory}
    {ctx : Word} (hs : c.body[i]? = some s) (hx : s.exec ρ mem ctx = some (ρ', mem'))
    (hP : PendInv c i ρ mem ctx) : PendInv c (i + 1) ρ' mem' ctx := by
  intro y j r hd hj hst hl
  have hbody : c.body[j]? = some (.assign y r) := defSites_spec (hc.defs ▸ hd)
  obtain ⟨hother, hmem⟩ := exec_other hx
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [window_succ (Nat.le_of_lt hj) hs] at hst
    have hlen : j < c.body.length := by
      have := List.getElem?_eq_some_iff.1 hbody; exact this.1
    obtain ⟨hst', hs'⟩ := stableFrom_snoc (window_ne_nil hj hlen) hst
    obtain ⟨v, hv, hev⟩ := hP y j r hd hj hst' (fun w e m he => pure_succ (hl w e m he))
    have hs'' := all_avoid hs'
    have hy : y ∉ s.defs := fun h' => (hs'' y h').1 rfl
    have hu : ∀ u ∈ r.uses, u ∉ s.defs := fun u hu h' => (hs'' u h').2 hu
    refine ⟨v, (hother y hy).trans hv, ?_⟩
    rw [Rhs.eval_congr (fun u hu' => hother u (hu u hu')) (fun ⟨w, e, m, he⟩ => hmem (pure_not_effect hc hj hs
      (hl w e m he)))]
    exact hev
  · rw [hs] at hbody
    cases hbody
    have hw : (c.body.drop j).take (j + 1 - j) = [.assign y r] := by
      rw [show j + 1 - j = 1 by omega, List.take_one, List.head?_drop, hs]
      rfl
    rw [hw] at hst
    have hyr : y ∉ r.uses := stableFrom_single hst y (by simp [Lir.Stmt.defs])
    simp only [Lir.Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.mk.injEq] at hx
    obtain ⟨v, hv, rfl, rfl⟩ := hx
    refine ⟨v, by simp, ?_⟩
    rw [Rhs.eval_congr (fun u hu => insert_ne (t := y) (fun h' => hyr (by rw [h']; exact hu))) (fun _ => rfl)]
    exact hv

/-- A call keeps the stable values its results do not overwrite pending;
no load is pending across it. -/
theorem PendInv.call {c : Ctx} (hc : BlockCtx c) {i : Nat} {rs : List VReg} {g : Lir.FunId} {as : List Lir.Arg}
    {ρ : Env} {mem : X86.Memory} {ctx : Word} (hs : c.body[i]? = some (.call rs g as)) (hP : PendInv c i ρ mem ctx)
    (ρ' : Env) (mem' : X86.Memory) (hρ : ∀ u, u ∉ rs → ρ'[u]? = ρ[u]?) : PendInv c (i + 1) ρ' mem' ctx := by
  intro y j r hd hj hst hl
  have hbody : c.body[j]? = some (.assign y r) := defSites_spec (hc.defs ▸ hd)
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [window_succ (Nat.le_of_lt hj) hs] at hst
    have hlen : j < c.body.length := by
      have := List.getElem?_eq_some_iff.1 hbody; exact this.1
    obtain ⟨hst', hs'⟩ := stableFrom_snoc (window_ne_nil hj hlen) hst
    have hnl : ∀ w e m, r ≠ .load w e m := fun w e m he => by
      have := pure_not_effect hc hj hs (hl w e m he)
      simp [Lir.Stmt.isEffect] at this
    obtain ⟨v, hv, hev⟩ := hP y j r hd hj hst' (fun w e m he => absurd he (hnl w e m))
    have hs'' := all_avoid hs'
    have hy : y ∉ rs := fun h' => (hs'' y h').1 rfl
    have hu : ∀ u ∈ r.uses, u ∉ rs := fun u hu h' => (hs'' u h').2 hu
    refine ⟨v, (hρ y hy).trans hv, ?_⟩
    rw [Rhs.eval_congr (fun u hu' => hρ u (hu u hu')) (fun ⟨w, e, m, he⟩ => absurd he (hnl w e m))]
    exact hev
  · rw [hs] at hbody
    cases hbody

/-- The pending facts at a site, from the invariant: each newly folded
statement is stable up to the site. -/
theorem PendInv.pend {c c' : Ctx} (hc : BlockCtx c) (hdefs : c'.defs = c.defs) (hbody : c'.body = c.body)
    (heff : c'.effects = c.effects) {st st' : St} (hext : Ext c' st st') {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (hP : PendInv c c'.pos ρ mem ctx) : Pend c' st st' ρ mem ctx := by
  intro y j r hd hj hn
  obtain ⟨_, F, hF, hfold⟩ := hext
  rw [hF] at hj
  rcases List.mem_append.1 hj with hj | hj
  · obtain ⟨⟨y', r', hd', hst, hl⟩, hlt⟩ := hfold j hj
    rw [hdefs] at hd hd'
    obtain ⟨rfl, rfl⟩ := defSites_unique (hc.defs ▸ hd) (hc.defs ▸ hd')
    rw [hbody] at hst
    rw [heff] at hl
    exact hP y j r hd hlt hst hl
  · exact absurd hj hn

end Compilatrix.Xv.Select.Proof
