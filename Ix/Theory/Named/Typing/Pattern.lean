/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.VExpr

open Ix.Theory (VLevel)

namespace Ix.Theory.Named

open VExpr

inductive Pattern where
  | const (c : Name)
  | app (f a : Pattern)
  | var (f : Pattern)

@[reducible] def Pattern.varN (p : Pattern) : Nat → Pattern
  | 0 => p
  | n+1 => (p.varN n).var

inductive Subpattern (p : Pattern) : Pattern → Prop where
  | refl : Subpattern p p
  | appL : Subpattern p f → Subpattern p (.app f a)
  | appR : Subpattern p a → Subpattern p (.app f a)
  | varL : Subpattern p f → Subpattern p (.var f)

theorem Subpattern.varN (h : Subpattern p f) : ∀ {n}, Subpattern p (.varN f n)
  | 0 => h
  | _+1 => .varL (.varN h)

theorem Subpattern.trans {p₁ p₂ p₃} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₃) : Subpattern p₁ p₃ := by
  induction H₂ with
  | refl => exact H₁
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | varL _ ih => exact .varL ih

theorem Subpattern.sizeOf_le {p₁ p₂} (H₁ : Subpattern p₁ p₂) : sizeOf p₁ ≤ sizeOf p₂ := by
  induction H₁ <;> simp <;> omega

theorem Subpattern.antisymm {p₁ p₂} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₁) : p₂ = p₁ := by
  cases id H₂ with
  | refl => rfl
  | _ h₂ =>
    have H₁ := H₁.sizeOf_le
    have h₂ := h₂.sizeOf_le
    simp at H₁; omega

inductive Arity (p : Pattern) : Nat → Pattern → Prop where
  | refl : Arity p 0 p
  | app : Arity p n f → Arity p (n+1) (.app f a)
  | var : Arity p n f → Arity p (n+1) (.var f)

theorem Arity.subpattern : Arity p n p' → Subpattern p p'
  | .refl => .refl
  | .app h => .appL h.subpattern
  | .var h => .varL h.subpattern

def Pattern.inter : Pattern → Pattern → Option Pattern
  | .const c, .const c' => if c = c' then some (.const c) else none
  | .app f a, .app f' a' => return .app (← f.inter f') (← a.inter a')
  | .var f, .var f' => return .var (← f.inter f')
  | .app f a, .var f' => return .app (← f.inter f') a
  | .var f, .app f' a' => return .app (← f.inter f') a'
  | _, _ => none

theorem Pattern.inter_self (p : Pattern) : p.inter p = some p := by induction p <;> simp [*, inter]

theorem Pattern.inter_comm (p q : Pattern) : p.inter q = q.inter p := by
  induction p generalizing q <;> cases q <;> simp [*, eq_comm, inter] <;> split <;> simp [*]

inductive Pattern.LE : Pattern → Pattern → Prop where
  | refl : LE p p
  | var : LE f f' → LE (.var f) (.var f')
  | app : LE f f' → LE a a' → LE (.app f a) (.app f' a')
  | app_var : LE f f' → LE (.app f a) (.var f')

@[reducible] def Pattern.Path : Pattern → Type
  | .const _ => Empty
  | .app f a => f.Path ⊕ a.Path
  | .var f => Option f.Path

inductive Pattern.Matches : (p : Pattern) → VExpr → List VLevel → (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) ls nofun
  | var : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : Matches f f' f1 g1 → Matches a a' f2 g2 →
    Matches (.app f a) (.app f' a') f1 (Sum.elim g1 g2)

theorem Pattern.Matches.uniq {p : Pattern} {e : VExpr} {m1 m2 m1' m2'}
    (H1 : Pattern.Matches p e m1 m2) (H2 : Pattern.Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction H1 generalizing m1' with cases H2
  | const => simp
  | var _ ih => rename_i h; simp [ih h]
  | app _ _ ih1 ih2 => rename_i h2 h1; simp [ih1 h1, ih2 h2]

def Pattern.OnArgs (P : VExpr → Prop) : Pattern → Prop
  | .const .. => True
  | .var f => f.OnArgs P
  | .app f a => f.OnArgs P ∧ a.OnArgs P ∧ ∀ e m1 m2, a.Matches e m1 m2 → P e

inductive Pattern.RHS (p : Pattern) where
  | fixed (c : VExpr) (_ : c.Closed)
  | app (f a : RHS p)
  | var (e : p.Path)

inductive Pattern.Check (p : Pattern) where
  | true
  | defeq (x y : RHS p) (rest : Check p)

def Pattern.RHS.apply {p : Pattern} (m1 : List VLevel) (m2 : p.Path → VExpr) : p.RHS → VExpr
  | .fixed c _ => c.instL m1
  | .var path => m2 path
  | .app f a => .app (f.apply m1 m2) (a.apply m1 m2)

theorem Pattern.RHS.lift'_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).lift' ρ = (r.apply m1 fun x => (m2 x).lift' ρ) := by
  induction r <;> simp [*, apply, lift', ← instL_lift']
  rw [ClosedN.lift'_eq ‹_› (by trivial)]

theorem Pattern.RHS.liftN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).liftN n k = (r.apply m1 fun x => (m2 x).liftN n k) := by
  simp [← lift'_consN_skipN, lift'_apply]

theorem Pattern.matches_lift' {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).lift' ρ := by
  constructor
  · intro h; generalize eq : e.lift' ρ = e' at h
    induction h generalizing e with
    | const => cases e <;> cases eq; exact ⟨_, .const, nofun⟩
    | var _ ih =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih rfl
      refine ⟨_, .var l1, ?_⟩
      rintro (_|_) <;> solve_by_elim
    | app _ _ ih1 ih2 =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih1 rfl
      have ⟨_, r1, r2⟩ := ih2 rfl
      refine ⟨_, .app l1 r1, ?_⟩
      rintro (_|_) <;> solve_by_elim
  · intro ⟨m2, h1, h2⟩
    induction h1 with
    | const => exact (show m2' = _ by ext ⟨⟩) ▸ .const
    | var _ ih =>
      have := (ih (h2 <| some ·)).var (a' := ?_)
      rwa [(_ : m2' = _)]; ext (_|_) <;> simp [h2 none]
    | app _ _ ih1 ih2 =>
      have := (ih1 (h2 <| .inl ·)).app (ih2 (h2 <| .inr ·))
      rwa [(_ : m2' = _)]; ext (_|_) <;> rfl

theorem Pattern.matches_liftN {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.liftN n k) m1 m2' ↔ ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).liftN n k := by
  simp only [← lift'_consN_skipN]; exact p.matches_lift'

theorem Pattern.RHS.instN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).inst e₀ k = (r.apply m1 fun x => (m2 x).inst e₀ k) := by
  induction r <;> simp [*, apply, inst]
  rw [(ClosedN.instL ‹_›).instN_eq (Nat.zero_le _)]

theorem Pattern.matches_instN {p : Pattern} {e : VExpr} {m1 m2} (H : p.Matches e m1 m2) :
    p.Matches (e.inst e₀ k) m1 fun x => (m2 x).inst e₀ k := by
  induction H with
  | const => erw [show (fun _ : Empty => _) = _ by ext ⟨⟩]; exact .const
  | var _ ih =>
    rw [(_ : (fun _ => _) = _)]; exact ih.var
    ext (_|_) <;> rfl
  | app _ _ ih1 ih2 =>
    rw [(_ : (fun _ => _) = _)]; exact ih1.app ih2
    ext (_|_) <;> rfl

/-- Universe instantiation preserves a successful match.  The universe
capture is instantiated pointwise and every expression capture is
instantiated by the same level substitution. -/
theorem Pattern.Matches.instL {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) (ls : List VLevel) :
    p.Matches (e.instL ls) (m1.map (VLevel.inst ls))
      fun x => (m2 x).instL ls := by
  induction H with
  | const => erw [show (fun _ : Empty => _) = _ by ext ⟨⟩]; exact .const
  | var _ ih =>
    rw [(_ : (fun _ => _) = _)]; exact ih.var
    ext (_|_) <;> rfl
  | app _ _ ih1 ih2 =>
    rw [(_ : (fun _ => _) = _)]; exact ih1.app ih2
    ext (_|_) <;> rfl

theorem Pattern.matches_inter {p q : Pattern} {e : VExpr} :
    (∃ m1 m2, p.Matches e m1 m2) ∧ (∃ m1 m2, q.Matches e m1 m2) ↔
    (∃ r m1 m2, p.inter q = some r ∧ r.Matches e m1 m2) := by
  constructor
  · rintro ⟨⟨m1, m2, hp⟩, ⟨m3, m4, hq⟩⟩
    induction hp generalizing q m3 <;> cases hq <;> simp [inter]
    · case const.const => exact ⟨_, _, .const⟩
    · case var.var ih _ _ ih' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ih _ _ ih'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .var hf2⟩
    · case var.app ihf _ _ _ _ _ ha2 ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.var ha2 ihf _ _ _ ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.app ihf iha _ _ _ _ _ iha' ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      have ⟨ra, ma1, ma2, ha1, ha2⟩ := iha _ _ iha'
      exact ⟨_, ⟨_, hf1, _, ha1, rfl⟩, _, _, .app hf2 ha2⟩
  · rintro ⟨r, m1, m2, h1, h2⟩
    induction p generalizing q e r m1 <;> cases q <;> simp [inter] at h1 <;> [
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨_, wf, _, wa, rfl⟩ := h1;
        obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1
      ] <;> cases h2
    · exact ⟨⟨_, _, .const⟩, ⟨_, _, .const⟩⟩
    · next ihf iha _ _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      have ⟨⟨ma1, ma2, ha⟩, ⟨ma1', ma2', ha'⟩⟩ := iha _ _ _ wa ha
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .var hf'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha' hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .var hf'⟩⟩

theorem Pattern.matches_determ
    (h1 : Matches p e m1 m2) (h2 : Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction h1 generalizing m1' with
  | const => let .const := h2; simp
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]
  | var l1 ih1 => let .var r1 := h2; simp [ih1 r1]

def Pattern.Check.OK (defeq : VExpr → VExpr → Prop) {p : Pattern}
    (m1 : List VLevel) (m2 : p.Path → VExpr) : p.Check → Prop
  | .true => True
  | .defeq a b rest => defeq (RHS.apply m1 m2 a) (RHS.apply m1 m2 b) ∧ rest.OK defeq m1 m2

theorem Pattern.Check.OK.map
    {df df' : VExpr → VExpr → Prop} {p : Pattern} {ck : p.Check} {m1 m2 m1' m2'}
    (h : ∀ a b : p.RHS,
      df (a.apply m1 m2) (b.apply m1 m2) → df' (a.apply m1' m2') (b.apply m1' m2'))
    (H : ck.OK df m1 m2) : ck.OK df' m1' m2' := by
  induction ck <;> simp [OK, *] at H ⊢; cases H; constructor <;> solve_by_elim

inductive SimplePattern where
  | iota (recursor : Name) (major : Nat) (constr : Name) (args : Nat)
  | defn (head : Name)

@[reducible] def SimplePattern.toPattern : SimplePattern → Pattern
  | .defn c => .const c
  | .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)

/-! ## Shape helpers for generated recursor patterns

`HeadConstN`, `HeadConst`, `of_varN_matches`, `RecursorIotaPattern`, and
`matches_shape` form the implementation-independent shape layer consumed by
the generated iota patterns of a certified inductive block
(`Theory/Typing/InductivePattern.lean`). They characterize matching against
`Pattern.varN` towers and `SimplePattern.iota` patterns without referring to
any generator data. -/

/-- `HeadConstN c ls n e`: `e` is the constant `c` at levels `ls` applied to
exactly `n` arguments. This is the expression shape captured by matching the
pattern `Pattern.varN (.const c) n`. -/
inductive HeadConstN (c : Name) (ls : List VLevel) : Nat → VExpr → Prop where
  | const : HeadConstN c ls 0 (.const c ls)
  | app : HeadConstN c ls n f → HeadConstN c ls (n+1) (.app f a)

/-- `e` is an application spine headed by the constant `c`. -/
def HeadConst (c : Name) (e : VExpr) : Prop := ∃ ls n, HeadConstN c ls n e

/-- Matching a `varN` tower of a constant captures exactly a `HeadConstN`
spine whose head levels are the pattern's level assignment. -/
theorem Pattern.of_varN_matches {c : Name} :
    ∀ {n : Nat} {e : VExpr} {m2}, (Pattern.varN (.const c) n).Matches e m1 m2 →
      HeadConstN c m1 n e := by
  intro n
  induction n with
  | zero => intro e m2 H; cases H; exact .const
  | succ n ih => intro e m2 H; cases H with | var h => exact .app (ih h)

/-- Every `HeadConstN` spine matches its `varN` tower. -/
theorem HeadConstN.matches : HeadConstN c ls n e →
    ∃ m2, (Pattern.varN (.const c) n).Matches e ls m2
  | .const => ⟨_, .const⟩
  | .app h => let ⟨_, h'⟩ := h.matches; ⟨_, .var h'⟩

/-- The capture paths of an `n`-ary `varN` tower in argument order (outermost
application first): matching assigns the `t`-th entry the `t`-th spine
argument. -/
def Pattern.varNPaths (p : Pattern) : ∀ n, List (Pattern.Path (p.varN n))
  | 0 => []
  | n+1 => (varNPaths p n).map some ++ [none]

@[simp] theorem Pattern.varNPaths_length (p : Pattern) :
    ∀ n, (varNPaths p n).length = n
  | 0 => rfl
  | n+1 => by
    show ((varNPaths p n).map some ++ [none]).length = n + 1
    rw [List.length_append, List.length_map, varNPaths_length p n]; rfl

/-- The exact pattern of one generated iota rule: the recursor constant
applied to `major` arguments (parameters, motives, minors, and the
constructor's result indices), with a `ctor`-headed major premise carrying
`args` arguments. Definitionally `(SimplePattern.iota recursor major ctor
args).toPattern`. -/
def RecursorIotaPattern (recursor : Name) (major : Nat)
    (ctor : Name) (args : Nat) : Pattern :=
  .app (.varN (.const recursor) major) (.varN (.const ctor) args)

theorem SimplePattern.toPattern_iota :
    (SimplePattern.iota r m c n).toPattern = RecursorIotaPattern r m c n := rfl

/-- Match inversion for an iota pattern: the expression is exactly a
recursor-headed spine at the pattern's level assignment whose last argument
is a constructor-headed spine (at unconstrained levels). -/
theorem RecursorIotaPattern.matches_shape
    (H : (RecursorIotaPattern r mj c n).Matches e m1 m2) :
    ∃ f a ls, e = .app f a ∧ HeadConstN r m1 mj f ∧ HeadConstN c ls n a := by
  cases H with
  | app h1 h2 =>
    exact ⟨_, _, _, rfl, Pattern.of_varN_matches h1, Pattern.of_varN_matches h2⟩

/-- Match construction for an iota pattern from the two head spines. -/
theorem RecursorIotaPattern.matches_of
    (h1 : HeadConstN r ls mj f) (h2 : HeadConstN c ls' n a) :
    ∃ m2, (RecursorIotaPattern r mj c n).Matches (.app f a) ls m2 :=
  let ⟨_, hf⟩ := h1.matches
  let ⟨_, ha⟩ := h2.matches
  ⟨_, .app hf ha⟩

/-- Subpatterns of a constant `varN` tower are exactly its shorter towers. -/
theorem Subpattern.varN_const_le :
    ∀ {n}, Subpattern p (Pattern.varN (.const c) n) →
      ∃ j, j ≤ n ∧ p = Pattern.varN (.const c) j := by
  intro n
  induction n with
  | zero => intro H; cases H; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ n ih =>
    intro H
    cases H with
    | refl => exact ⟨n+1, Nat.le_refl _, rfl⟩
    | varL h =>
      let ⟨j, hj, hp⟩ := ih h
      exact ⟨j, Nat.le_succ_of_le hj, hp⟩

/-- Subpattern classification for an iota pattern: the whole pattern, a
prefix of the recursor head, or a prefix of the constructor spine. -/
theorem RecursorIotaPattern.subpattern_inv
    (H : Subpattern p (RecursorIotaPattern r mj c n)) :
    p = RecursorIotaPattern r mj c n ∨
      (∃ j, j ≤ mj ∧ p = .varN (.const r) j) ∨
      (∃ j, j ≤ n ∧ p = .varN (.const c) j) := by
  cases H with
  | refl => exact .inl rfl
  | appL h => exact .inr (.inl h.varN_const_le)
  | appR h => exact .inr (.inr h.varN_const_le)

/-- Two constant `varN` towers intersect only when they agree exactly. -/
theorem Pattern.varN_const_inter_some :
    ∀ {n n' p}, (Pattern.varN (.const c) n).inter (Pattern.varN (.const c') n') = some p →
      c = c' ∧ n = n' ∧ p = Pattern.varN (.const c) n := by
  intro n
  induction n with
  | zero =>
    intro n' p h
    cases n' with
    | zero =>
      simp [Pattern.inter] at h
      exact ⟨h.1, rfl, h.2.symm⟩
    | succ n' => simp [Pattern.inter] at h
  | succ n ih =>
    intro n' p h
    cases n' with
    | zero => simp [Pattern.inter] at h
    | succ n' =>
      simp only [Pattern.inter, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨q, hq, rfl⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih hq
      exact ⟨rfl, rfl, rfl⟩

theorem Pattern.varN_const_inter_of_ne_name (h : c ≠ c') (n n' : Nat) :
    (Pattern.varN (.const c) n).inter (Pattern.varN (.const c') n') = none := by
  cases e : (Pattern.varN (.const c) n).inter (Pattern.varN (.const c') n') with
  | none => rfl
  | some p => exact absurd (varN_const_inter_some e).1 h

theorem Pattern.varN_const_inter_of_ne_arity (h : n ≠ n') (c c' : Name) :
    (Pattern.varN (.const c) n).inter (Pattern.varN (.const c') n') = none := by
  cases e : (Pattern.varN (.const c) n).inter (Pattern.varN (.const c') n') with
  | none => rfl
  | some p => exact absurd (varN_const_inter_some e).2.1 h

/-- An application pattern intersects a constant `varN` tower only through a
positive tower whose inner tower intersects the function part. -/
theorem Pattern.app_inter_varN_const_some {f a : Pattern}
    (h : (Pattern.app f a).inter (Pattern.varN (.const c) n) = some p) :
    ∃ n' q, n = n' + 1 ∧ f.inter (Pattern.varN (.const c) n') = some q ∧
      p = .app q a := by
  cases n with
  | zero => simp [Pattern.inter] at h
  | succ n' =>
    simp only [Pattern.inter, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact ⟨n', q, rfl, hq, rfl⟩

/-- Two iota patterns intersect only when they agree exactly. -/
theorem RecursorIotaPattern.inter_some
    (h : (RecursorIotaPattern r mj c n).inter (RecursorIotaPattern r' mj' c' n') = some p) :
    r = r' ∧ mj = mj' ∧ c = c' ∧ n = n' ∧ p = RecursorIotaPattern r mj c n := by
  simp only [RecursorIotaPattern, Pattern.inter, bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨q1, h1, q2, h2, rfl⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := Pattern.varN_const_inter_some h1
  obtain ⟨rfl, rfl, rfl⟩ := Pattern.varN_const_inter_some h2
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An iota pattern intersects a constant `varN` tower only at a tower whose
inner arity is the pattern's major arity with the recursor's name. -/
theorem RecursorIotaPattern.inter_varN_const_some
    (h : (RecursorIotaPattern r mj c n).inter (Pattern.varN (.const b) j) = some p) :
    b = r ∧ j = mj + 1 := by
  obtain ⟨j', q, rfl, hq, rfl⟩ := Pattern.app_inter_varN_const_some h
  obtain ⟨rfl, rfl, rfl⟩ := Pattern.varN_const_inter_some hq
  exact ⟨rfl, rfl⟩

/-- Constant `varN` towers are injective in the head name and the arity. -/
theorem Pattern.varN_const_inj {c c' : Name} :
    ∀ {n n' : Nat}, Pattern.varN (.const c) n = Pattern.varN (.const c') n' →
      c = c' ∧ n = n'
  | 0, 0, h => by cases h; exact ⟨rfl, rfl⟩
  | 0, n'+1, h => absurd h (by simp [Pattern.varN])
  | n+1, 0, h => absurd h (by simp [Pattern.varN])
  | n+1, n'+1, h => by
    injection h with h1
    obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj h1
    exact ⟨rfl, rfl⟩

/-- Iota patterns are injective in all four components. -/
theorem RecursorIotaPattern.inj
    (h : RecursorIotaPattern r mj c n = RecursorIotaPattern r' mj' c' n') :
    r = r' ∧ mj = mj' ∧ c = c' ∧ n = n' := by
  injection h with h1 h2
  obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj h1
  obtain ⟨rfl, rfl⟩ := Pattern.varN_const_inj h2
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The only application subpattern of an iota pattern is the pattern
itself. -/
theorem RecursorIotaPattern.app_subpattern
    (H : Subpattern (.app p₁ p₂) (RecursorIotaPattern r mj c n)) :
    p₁ = .varN (.const r) mj ∧ p₂ = .varN (.const c) n := by
  rcases RecursorIotaPattern.subpattern_inv H with heq | ⟨j, hj, heq⟩ | ⟨j, hj, heq⟩
  · injection heq with h1 h2; exact ⟨h1, h2⟩
  · cases j <;> exact absurd heq (by simp [Pattern.varN])
  · cases j <;> exact absurd heq (by simp [Pattern.varN])

/-- Apply an RHS template head to a list of template arguments. -/
def Pattern.RHS.appN {p : Pattern} (f : p.RHS) : List p.RHS → p.RHS
  | [] => f
  | a :: as => Pattern.RHS.appN (.app f a) as
