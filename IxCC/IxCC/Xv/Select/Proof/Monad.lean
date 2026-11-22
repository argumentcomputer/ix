import IxCC.Xv.Select.Proof.Lin

/-!
# Running selection's monad

Selection's rules run in `SelM` (a reader over the block's analyses and a
state of fresh registers and consumed statements). This module inverts its
binds and primitives, and defines what every rule guarantees of the state:
fresh registers only grow, and every statement a rule consumes is a fold of
the current site (`Folded`): an assignment of the block before the site,
whose operands no statement up to the site redefines, and, for a load, with
no store or call in between. `Pend` is what the consumed statements give a
Lir environment at the site: each folded register holds its right-hand
side's value.
-/

namespace IxCC.Xv.Select.Proof

open IxCC.Lir (VReg Word Env)
open IxCC.Xv.Select

/-! ## Binds and primitives -/

theorem bind_ok {α β : Type} {f : SelM α} {g : α → SelM β} {c : Ctx} {st st'' : St} {b : β} :
    (f >>= g) c st = .ok (b, st'') ↔ ∃ a st', f c st = .ok (a, st') ∧ g a c st' = .ok (b, st'') := by
  show (do let (a, s) ← f c st; g a c s) = _ ↔ _
  cases h : f c st with
  | error e => simp [bind, Except.bind]
  | ok p =>
    obtain ⟨a, s⟩ := p
    simp only [bind, Except.bind, Except.ok.injEq]
    constructor
    · intro hg; exact ⟨a, s, rfl, hg⟩
    · rintro ⟨a', s', he, hg⟩
      cases he
      exact hg

theorem pure_ok {α : Type} {a b : α} {c : Ctx} {st st' : St} :
    (pure a : SelM α) c st = .ok (b, st') ↔ a = b ∧ st = st' := by
  simp [pure, ReaderT.pure, StateT.pure, Except.pure]

def fireSt (n : String) (s : St) : St :=
  if s.stats then { s with fired := s.fired.insert n (s.fired.getD n 0 + 1) } else s

@[simp] theorem fireSt_next (n : String) (s : St) : (fireSt n s).next = s.next := by
  unfold fireSt; split <;> rfl

@[simp] theorem fireSt_consumed (n : String) (s : St) : (fireSt n s).consumed = s.consumed := by
  unfold fireSt; split <;> rfl

theorem fire_run (n : String) (c : Ctx) (st : St) : fire n c st = .ok ((), fireSt n st) := rfl

theorem fresh_run (c : Ctx) (st : St) : fresh c st = .ok (st.next, { st with next := st.next + 1 }) := rfl

theorem consume_run (j : Nat) (c : Ctx) (st : St) :
    consume j c st = .ok ((), { st with consumed := j :: st.consumed }) := rfl

theorem useCount_run (x : VReg) (c : Ctx) (st : St) : useCount x c st = .ok (c.uses.getD x 0, st) := rfl

theorem read_run (c : Ctx) (st : St) : (read : SelM Ctx) c st = .ok (c, st) := rfl

theorem get_run (c : Ctx) (st : St) : (get : SelM St) c st = .ok (st, st) := rfl

theorem singleUse_run (x : VReg) (c : Ctx) (st : St) : singleUse x c st = .ok (c.uses.getD x 0 == 1, st) := rfl

theorem sitePos_run (c : Ctx) (st : St) : sitePos c st = .ok (c.site.getD c.size, st) := rfl

theorem pureBetween_run (j i : Nat) (c : Ctx) (st : St) :
    pureBetween j i c st = .ok (c.effects.all fun p => p ≤ j || i ≤ p, st) := rfl

/-! Binds after a primitive, as equations simp can run. -/

section Steps

variable {β : Type} {c : Ctx} {st : St}

@[simp] theorem read_bind (g : Ctx → SelM β) : ((read : SelM Ctx) >>= g) c st = g c c st := rfl
@[simp] theorem get_bind (g : St → SelM β) : ((get : SelM St) >>= g) c st = g st c st := rfl
@[simp] theorem sitePos_bind (g : Nat → SelM β) : (sitePos >>= g) c st = g (c.site.getD c.size) c st := rfl
@[simp] theorem fire_bind (n : String) (g : Unit → SelM β) : (fire n >>= g) c st = g () c (fireSt n st) := rfl
@[simp] theorem fresh_bind (g : VReg → SelM β) :
    (fresh >>= g) c st = g st.next c { st with next := st.next + 1 } := rfl
@[simp] theorem consume_bind (j : Nat) (g : Unit → SelM β) :
    (consume j >>= g) c st = g () c { st with consumed := j :: st.consumed } := rfl
@[simp] theorem useCount_bind (x : VReg) (g : Nat → SelM β) :
    (useCount x >>= g) c st = g (c.uses.getD x 0) c st := rfl
@[simp] theorem singleUse_bind (x : VReg) (g : Bool → SelM β) :
    (singleUse x >>= g) c st = g (c.uses.getD x 0 == 1) c st := rfl
@[simp] theorem pureBetween_bind (j i : Nat) (g : Bool → SelM β) :
    (pureBetween j i >>= g) c st = g (c.effects.all fun p => p ≤ j || i ≤ p) c st := rfl
@[simp] theorem pure_run (a : β) : (pure a : SelM β) c st = .ok (a, st) := rfl
@[simp] theorem pure_bind' {α : Type} (a : α) (g : α → SelM β) : (pure a >>= g) c st = g a c st := rfl

end Steps

/-- Run selection's primitives and decided branches in a hypothesis or goal. -/
macro "sel_simp" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic => `(tactic|
  simp only [$xs,*, read_bind, get_bind, sitePos_bind, fire_bind, fresh_bind, consume_bind, useCount_bind,
    singleUse_bind, pureBetween_bind, pure_run, pure_bind', ↓reduceIte, Bool.false_eq_true,
    Except.ok.injEq, Prod.mk.injEq] at $h:ident)

/-- `omega` over registers: `VReg` is `Nat`, which `omega` does not unfold. -/
macro "vomega" : tactic => `(tactic| (try simp only [IxCC.Lir.VReg] at *) <;> omega)

theorem unsupported_ne {α : Type} {form reason : String} {c : Ctx} {st st' : St} {a : α} :
    (unsupported form reason : SelM α) c st ≠ .ok (a, st') := by
  intro h
  have e : (unsupported form reason : SelM α) c st = .error ⟨c.fn, c.label, c.site, form, reason⟩ := rfl
  rw [e] at h
  cases h

/-! ## Folds -/

/-- The current site's position. -/
def _root_.IxCC.Xv.Select.Ctx.pos (c : Ctx) : Nat := c.site.getD c.size

/-- Statement `j` of the block is folded into the current site: an
assignment of some register before the site whose operands no statement of
the window up to the site redefines (nor, after `j`, the register), and a
load only with no store or call between it and the site. -/
structure Folded (c : Ctx) (j : Nat) : Prop where
  def_ : ∃ y r, c.defs[y]? = some (j, r) ∧
    stableFrom y r ((c.body.drop j).take (c.pos - j)) = true ∧
    (∀ w e m, r = .load w e m → (c.effects.all fun p => p ≤ j || c.pos ≤ p) = true)
  before : j < c.pos

/-- Selection state `st'` extends `st` at context `c`: fresh registers only
grow, and every newly consumed statement is a fold of this site. -/
structure Ext (c : Ctx) (st st' : St) : Prop where
  next : st.next ≤ st'.next
  consumed : ∃ F, st'.consumed = F ++ st.consumed ∧ ∀ j ∈ F, Folded c j

theorem Ext.refl (c : Ctx) (st : St) : Ext c st st := ⟨Nat.le_refl _, [], rfl, by simp⟩

theorem Ext.trans {c : Ctx} {st st' st'' : St} (h₁ : Ext c st st') (h₂ : Ext c st' st'') : Ext c st st'' := by
  obtain ⟨hn₁, F₁, hc₁, hf₁⟩ := h₁
  obtain ⟨hn₂, F₂, hc₂, hf₂⟩ := h₂
  refine ⟨Nat.le_trans hn₁ hn₂, F₂ ++ F₁, by rw [hc₂, hc₁, List.append_assoc], ?_⟩
  intro j hj
  rcases List.mem_append.1 hj with h | h
  · exact hf₂ j h
  · exact hf₁ j h

theorem Ext.of_same {c : Ctx} {st st' : St} (hn : st'.next = st.next) (hc : st'.consumed = st.consumed) :
    Ext c st st' := ⟨Nat.le_of_eq hn.symm, [], by simp [hc], by simp⟩

theorem Ext.of_le {c : Ctx} {st st' : St} (hn : st.next ≤ st'.next) (hc : st'.consumed = st.consumed) :
    Ext c st st' := ⟨hn, [], by simp [hc], by simp⟩

theorem Ext.fire (c : Ctx) (n : String) (st : St) : Ext c st (fireSt n st) := Ext.of_same (by simp) (by simp)

theorem Ext.fresh (c : Ctx) (st : St) : Ext c st { st with next := st.next + 1 } :=
  ⟨Nat.le_succ _, [], by simp, by simp⟩

theorem Ext.consumed_sub {c : Ctx} {st st' : St} (h : Ext c st st') : ∀ j ∈ st.consumed, j ∈ st'.consumed := by
  obtain ⟨_, F, hc, _⟩ := h
  intro j hj; rw [hc]; exact List.mem_append_right _ hj

/-! ## Pending facts -/

/-- At the site, each register a statement newly consumed between `st` and
`st'` defines holds its right-hand side's value. -/
def Pend (c : Ctx) (st st' : St) (ρ : Env) (mem : X86.Memory) (ctx : Word) : Prop :=
  ∀ (y : VReg) (j : Nat) (r : Lir.Rhs), c.defs[y]? = some (j, r) → j ∈ st'.consumed → j ∉ st.consumed →
    ∃ v, ρ[y]? = some v ∧ r.eval ρ mem ctx = some v

theorem Pend.left {c : Ctx} {st st' st'' : St} {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (h : Pend c st st'' ρ mem ctx) (h₂ : Ext c st' st'') : Pend c st st' ρ mem ctx :=
  fun y j r hd hj hn => h y j r hd (h₂.consumed_sub j hj) hn

theorem Pend.right {c : Ctx} {st st' st'' : St} {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (h : Pend c st st'' ρ mem ctx) (h₁ : Ext c st st') : Pend c st' st'' ρ mem ctx :=
  fun y j r hd hj hn => h y j r hd hj fun hs => hn (h₁.consumed_sub j hs)

theorem Pend.same {c : Ctx} {st st' : St} {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (hc : st'.consumed = st.consumed) : Pend c st st' ρ mem ctx :=
  fun _ _ _ _ hj hn => absurd (hc ▸ hj) hn

/-- Every register the context's assignments read or define is below `N`. -/
def CtxLow (c : Ctx) (N : Nat) : Prop :=
  ∀ (y : VReg) (j : Nat) (r : Lir.Rhs), c.defs[y]? = some (j, r) → y < N ∧ ∀ u ∈ r.uses, u < N

/-! ## `defStmt?` -/

theorem defStmt?_spec {x : VReg} {c : Ctx} {st st' : St} {res : Option (Nat × Lir.Rhs)}
    (h : defStmt? x c st = .ok (res, st')) :
    st' = st ∧ ∀ j r, res = some (j, r) → c.defs[x]? = some (j, r) ∧ j < c.pos ∧ j ∉ st.consumed ∧
      stableFrom x r ((c.body.drop j).take (c.pos - j)) = true := by
  unfold defStmt? at h
  simp only [read_bind] at h
  cases hd : c.defs[x]? with
  | none =>
    simp only [hd, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | some p =>
    obtain ⟨j, r⟩ := p
    sel_simp [hd] at h
    by_cases hj : j < c.site.getD c.size
    · sel_simp [hj] at h
      by_cases hc : st.consumed.contains j = true
      · sel_simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · sel_simp [hc] at h
        by_cases hs : stableFrom x r (List.take (c.site.getD c.size - j) (List.drop j c.body)) = true
        · sel_simp [hs] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨rfl, fun j' r' he => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨rfl, hj, by simpa using hc, hs⟩
        · sel_simp [hs] at h
          obtain ⟨rfl, rfl⟩ := h
          simp
    · sel_simp [hj] at h
      obtain ⟨rfl, rfl⟩ := h
      simp


/-! ## Folding address arithmetic -/

/-- `l` with `y`'s sum `sub` folded in: every occurrence of `y` replaced,
its multipliers summed. -/
def foldInto (l : Lin) (y : VReg) (sub : Lin) : Lin :=
  ({ l with terms := l.terms.filter (·.1 != .r y) } : Lin).add
    (sub.scale ((l.terms.filter (·.1 == .r y)).map (·.2)).sum)

/-- Statement `j`, `y := r`, may fold into the current site: it is the
block's last assignment of `y`, before the site, unconsumed, and stable up
to the site. -/
def FoldOk (c : Ctx) (st : St) (j : Nat) (y : VReg) (r : Lir.Rhs) : Prop :=
  c.defs[y]? = some (j, r) ∧ j < c.pos ∧ j ∉ st.consumed ∧
    stableFrom y r ((c.body.drop j).take (c.pos - j)) = true

theorem FoldOk.folded {c : Ctx} {st : St} {j : Nat} {y : VReg} {r : Lir.Rhs} (h : FoldOk c st j y r)
    (hl : ∀ w e m, r = .load w e m → (c.effects.all fun p => p ≤ j || c.pos ≤ p) = true) : Folded c j :=
  ⟨⟨y, r, h.1, h.2.2.2, hl⟩, h.2.1⟩

theorem foldOne_spec {l : Lin} {used : List Nat} :
    ∀ {ts : List (Base VReg × Nat)} {c : Ctx} {st st' : St} {res : Option (Lin × Nat)},
      foldOne l used ts c st = .ok (res, st') →
      st' = st ∧ ∀ l' j, res = some (l', j) → j ∉ used ∧
        ∃ y r sub, FoldOk c st j y r ∧ rhsLin r = some sub ∧ l' = foldInto l y sub
  | [], c, st, st', res, h => by
      simp only [foldOne, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | (t, m) :: rest, c, st, st', res, h => by
      simp only [foldOne] at h
      rw [bind_ok] at h
      obtain ⟨a, st₁, ha, hk⟩ := h
      have hatt : st₁ = st ∧ ∀ l' j, a = some (l', j) → j ∉ used ∧
          ∃ y r sub, FoldOk c st j y r ∧ rhsLin r = some sub ∧ l' = foldInto l y sub := by
        cases t with
        | ctx =>
          sel_simp [Option.some.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          simp
        | r x =>
          sel_simp [Option.some.injEq] at ha
          by_cases hu : (c.uses.getD x 0 == 1) = true
          · sel_simp [hu] at ha
            rw [bind_ok] at ha
            obtain ⟨d, st₂, hd, ha⟩ := ha
            obtain ⟨rfl, hds⟩ := defStmt?_spec hd
            cases d with
            | none => sel_simp [Option.some.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha; simp
            | some p =>
              obtain ⟨j, r⟩ := p
              obtain ⟨hdef, hj, hjc, hst⟩ := hds j r rfl
              sel_simp [Option.some.injEq] at ha
              by_cases hc : used.contains j = true
              · sel_simp [hc] at ha; obtain ⟨rfl, rfl⟩ := ha; simp
              · sel_simp [hc] at ha
                cases hr : rhsLin r with
                | none => sel_simp [hr] at ha; obtain ⟨rfl, rfl⟩ := ha; simp
                | some sub =>
                  sel_simp [hr] at ha
                  obtain ⟨rfl, rfl⟩ := ha
                  refine ⟨rfl, fun l' j' he => ?_⟩
                  split at he
                  · simp only [Option.some.injEq, Prod.mk.injEq] at he
                    obtain ⟨rfl, rfl⟩ := he
                    exact ⟨by simpa using hc, x, r, sub, ⟨hdef, hj, hjc, hst⟩, hr, rfl⟩
                  · cases he
          · sel_simp [hu] at ha; obtain ⟨rfl, rfl⟩ := ha; simp
      obtain ⟨rfl, hspec⟩ := hatt
      cases a with
      | some p =>
        sel_simp [Option.some.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨rfl, hspec⟩
      | none =>
        sel_simp [Option.some.injEq] at hk
        exact foldOne_spec hk

/-- What a run of folds guarantees: each folded statement may fold, none
is a load (it contributes address arithmetic), and the sum keeps its value
wherever the folded registers hold their right-hand sides' values. -/
structure FoldsTo (c : Ctx) (st : St) (F : List Nat) (l l' : Lin) : Prop where
  ok : ∀ j ∈ F, ∃ y r, FoldOk c st j y r ∧ (rhsLin r).isSome
  val : ∀ (ρ : Env) (mem : X86.Memory) (ctx a : Word),
    (∀ j ∈ F, ∀ (y : VReg) (r : Lir.Rhs), c.defs[y]? = some (j, r) → ∃ v, ρ[y]? = some v ∧ r.eval ρ mem ctx = some v) →
    linVal ρ ctx l = some a → linVal ρ ctx l' = some a
  low : ∀ N, CtxLow c N → LinLow N l → LinLow N l'

theorem FoldsTo.refl (c : Ctx) (st : St) (l : Lin) : FoldsTo c st [] l l :=
  ⟨by simp, fun _ _ _ _ _ h => h, fun _ _ h => h⟩

theorem foldLinFuel_spec :
    ∀ {fuel : Nat} {l : Lin} {used : List Nat} {c : Ctx} {st st' : St} {l' : Lin} {used' : List Nat},
      foldLinFuel fuel l used c st = .ok ((l', used'), st') →
      st' = st ∧ ∃ F, used' = F ++ used ∧ FoldsTo c st F l l'
  | 0, l, used, c, st, st', l', used', h => by
      simp only [foldLinFuel, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨rfl, [], rfl, FoldsTo.refl c st l⟩
  | fuel + 1, l, used, c, st, st', l', used', h => by
      simp only [foldLinFuel] at h
      rw [bind_ok] at h
      obtain ⟨a, st₁, ha, hk⟩ := h
      obtain ⟨rfl, hspec⟩ := foldOne_spec ha
      cases a with
      | none =>
        sel_simp [Option.some.injEq] at hk
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
        exact ⟨rfl, [], rfl, FoldsTo.refl c _ l⟩
      | some p =>
        obtain ⟨l₁, j⟩ := p
        simp only at hk
        obtain ⟨-, y, r, sub, hok, hr, rfl⟩ := hspec l₁ j rfl
        obtain ⟨rfl, F, rfl, hF⟩ := foldLinFuel_spec hk
        refine ⟨rfl, F ++ [j], by simp, ?_, ?_, ?_⟩
        · intro j' hj'
          rcases List.mem_append.1 hj' with h | h
          · exact hF.ok j' h
          · simp only [List.mem_singleton] at h; subst h; exact ⟨y, r, hok, by simp [hr]⟩
        · intro ρ mem ctx a hpend hl
          apply hF.val ρ mem ctx a (fun j' hj' => hpend j' (List.mem_append_left _ hj'))
          obtain ⟨v, hv, hrv⟩ := hpend j (by simp) y r hok.1
          exact fold_val hv (rhsLin_val hr hrv) hl
        · intro N hc hl
          apply hF.low N hc
          obtain ⟨_, huN⟩ := hc y j r hok.1
          exact linLow_fold hl (linLow_rhsLin hr huN) _

theorem foldLin_spec {l l' : Lin} {used : List Nat} {c : Ctx} {st st' : St}
    (h : foldLin l c st = .ok ((l', used), st')) : st' = st ∧ FoldsTo c st used l l' := by
  obtain ⟨rfl, F, rfl, hF⟩ := foldLinFuel_spec h
  exact ⟨rfl, by simpa using hF⟩

theorem commitFold_spec :
    ∀ {used : List Nat} {c : Ctx} {st st' : St}, commitFold used c st = .ok ((), st') →
      st'.next = st.next ∧ st'.consumed = used.reverse ++ st.consumed
  | [], c, st, st', h => by
      simp only [commitFold, List.forM, pure_run, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp
  | j :: js, c, st, st', h => by
      simp only [commitFold, List.forM] at h
      rw [bind_ok] at h
      obtain ⟨u, st₁, h₁, h₂⟩ := h
      simp only [consume_bind, fire_run, Except.ok.injEq, Prod.mk.injEq] at h₁
      obtain ⟨-, rfl⟩ := h₁
      obtain ⟨hn, hc⟩ := commitFold_spec (used := js) h₂
      refine ⟨by simp [hn], by simp [hc]⟩

/-- Committed folds extend the state. -/
theorem FoldsTo.ext {c : Ctx} {st st' : St} {F : List Nat} {l l' : Lin} (hF : FoldsTo c st F l l')
    (hn : st'.next = st.next) (hc : st'.consumed = F.reverse ++ st.consumed) : Ext c st st' := by
  refine ⟨Nat.le_of_eq hn.symm, F.reverse, hc, fun j hj => ?_⟩
  obtain ⟨y, r, hok, hr⟩ := hF.ok j (List.mem_reverse.1 hj)
  refine hok.folded fun w e m he => ?_
  subst he
  simp [rhsLin] at hr

/-- Pending facts for committed folds are what their value needs. -/
theorem FoldsTo.pend {c : Ctx} {st st' : St} {F : List Nat} {l l' : Lin} (hF : FoldsTo c st F l l')
    (hc : st'.consumed = F.reverse ++ st.consumed) {ρ : Env} {mem : X86.Memory} {ctx : Word}
    (h : Pend c st st' ρ mem ctx) :
    ∀ j ∈ F, ∀ (y : VReg) (r : Lir.Rhs), c.defs[y]? = some (j, r) → ∃ v, ρ[y]? = some v ∧ r.eval ρ mem ctx = some v := by
  intro j hj y r hd
  obtain ⟨y', r', hok, -⟩ := hF.ok j hj
  exact h y j r hd (by rw [hc]; exact List.mem_append_left _ (List.mem_reverse.2 hj)) hok.2.2.1

theorem buildAmode_spec {m : Lir.Addr} {c : Ctx} {st st' : St} {am : Amode VReg}
    (h : buildAmode m c st = .ok (am, st')) :
    Ext c st st' ∧ st'.next = st.next ∧
      (∀ N, CtxLow c N → (∀ u ∈ m.uses, u < N) → ∀ u ∈ am.regs, u < N) ∧
      ∀ ρ mem ctx addr, m.eval ρ ctx = some addr → Pend c st st' ρ mem ctx → am.evalV ρ ctx = some addr := by
  unfold buildAmode at h
  rw [bind_ok] at h
  obtain ⟨⟨l, used⟩, st₁, h₁, h⟩ := h
  obtain ⟨rfl, hF⟩ := foldLin_spec h₁
  simp only at h
  cases he : l.encode with
  | some a =>
    simp only [he] at h
    rw [bind_ok] at h
    obtain ⟨u, st₂, h₂, h⟩ := h
    sel_simp [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hn, hc⟩ := commitFold_spec h₂
    refine ⟨hF.ext hn hc, hn, ?_, ?_⟩
    · intro N hc' hm
      exact encode_low he (hF.low N hc' (linLow_ofAddr hm))
    · intro ρ mem ctx addr hm hp
      exact encode_val he (hF.val ρ mem ctx addr (hF.pend hc hp) (by rw [linVal_ofAddr]; exact hm))
  | none =>
    simp only [he] at h
    cases he' : (Lin.ofAddr m).encode with
    | some a =>
      sel_simp [he'] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Ext.refl c _, rfl, ?_, ?_⟩
      · intro N _ hm
        exact encode_low he' (linLow_ofAddr hm)
      · intro ρ mem ctx addr hm _
        exact encode_val he' (by rw [linVal_ofAddr]; exact hm)
    | none =>
      simp only [he'] at h
      exact absurd h unsupported_ne

/-- A sunk load: its address, folded, and its value read at any narrower
width. -/
theorem sinkLoad?_spec {y : VReg} {i bytes : Nat} {c : Ctx} {st st' : St} {res : Option (Amode VReg)}
    (h : sinkLoad? y i bytes c st = .ok (res, st')) (hi : i = c.pos) :
    Ext c st st' ∧ st'.next = st.next ∧ (res = none → st' = st) ∧ ∀ am, res = some am →
      (∀ N, CtxLow c N → y < N ∧ ∀ u ∈ am.regs, u < N) ∧
      ∀ ρ mem ctx, Pend c st st' ρ mem ctx → ∃ addr vy, ρ[y]? = some vy ∧ am.evalV ρ ctx = some addr ∧
        ∀ w' : X86.Width, w'.bytes ≤ bytes → mem.read? w' addr = .ok (w'.truncate vy) := by
  subst hi
  unfold sinkLoad? at h
  sel_simp [Option.some.injEq] at h
  by_cases hu : (c.uses.getD y 0 == 1) = true
  · sel_simp [hu] at h
    rw [bind_ok] at h
    obtain ⟨d, st₁, hd, h⟩ := h
    obtain ⟨rfl, hds⟩ := defStmt?_spec hd
    rcases d with _ | ⟨j, _ | _ | ⟨w, e, m⟩ | _ | _ | _⟩ <;>
      try (sel_simp [Option.some.injEq] at h; obtain ⟨rfl, rfl⟩ := h
           exact ⟨Ext.refl c _, rfl, fun _ => rfl, fun _ h => by cases h⟩)
    obtain ⟨hdef, hj, hjc, hst⟩ := hds j _ rfl
    sel_simp [Option.some.injEq] at h
    by_cases hc : (decide (w.bytes ≥ bytes) && c.effects.all fun p => p ≤ j || c.pos ≤ p) = true
    · sel_simp [hc] at h
      rw [bind_ok] at h
      obtain ⟨a, st₂, h₂, h⟩ := h
      sel_simp [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hext, hn, hlow, hval⟩ := buildAmode_spec h₂
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hjf : Folded c j := ⟨⟨y, _, hdef, hst, fun _ _ _ _ => hc.2⟩, hj⟩
      have hext' : Ext c st₂ (fireSt "load.sink" { st₂ with consumed := j :: st₂.consumed }) :=
        ⟨by simp, [j], by simp, by simpa using hjf⟩
      refine ⟨hext.trans hext', by simp [hn], fun h => (by cases h), fun am he => ?_⟩
      simp only [Option.some.injEq] at he
      subst he
      refine ⟨fun N hcl => ⟨(hcl y j _ hdef).1, hlow N hcl (hcl y j _ hdef).2⟩, fun ρ mem ctx hp => ?_⟩
      obtain ⟨v, hv, hev⟩ := hp y j _ hdef (by simp) hjc
      simp only [Lir.Rhs.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at hev
      obtain ⟨addr, haddr, hload⟩ := hev
      refine ⟨addr, v, hv, hval ρ mem ctx addr haddr (hp.left hext'), fun w' hw' => ?_⟩
      exact loadWord_read hload (Nat.le_trans hw' hc.1)
    · sel_simp [hc] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Ext.refl c _, rfl, fun _ => rfl, fun _ h => by cases h⟩
  · sel_simp [hu] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Ext.refl c _, rfl, fun _ => rfl, fun _ h => by cases h⟩

end IxCC.Xv.Select.Proof
