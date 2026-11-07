import IxCC.Rt.Proof.SwitchTag

/-!
# Switches: Lir takes Cfg's edge

Cfg's `switch` selects the first alternative with the scrutinee's key
(else the default); the lowering tests words and tags, which agree with
keys only on values of the alternatives' type: constructor tags repeat
across types, and a `Nat` literal's word is a field-less constructor's.
`Dispatches` states what the lowering needs: a switch with `Nat` keys
scrutinises a `Nat` literal, and each alternative's test (`Accepts`)
accepts the value exactly when the alternative's key is the value's. A
well-typed program has it (the keys and the value are one inductive's,
whose tags are distinct); `Rt.lower_correct` assumes it of every switch
its Cfg run executes.

`switch_sim`: under `Dispatches`, Lir runs from the switch's code to the
block that takes the lowered edge of the alternative Cfg selects.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-! ## What the lowering needs of a scrutinee -/

/-- The word of a value that is not a cell. -/
def valWord : Own.RVal → Option Word
  | .lit (.nat n) => natWord n
  | .ctor0 c => some (ctor0Word c.tag)
  | .erased => some erasedWord
  | _ => none

/-- Whether the lowered test of alternative key `k` accepts `v`. -/
def Accepts (T : Tables) (H : Own.Heap) (k : Key.CtorKey) (v : Own.RVal) : Prop :=
  match keyKind T k with
  | some .zero => v = .lit (.nat 0)
  | some .succ => ∃ n, v = .lit (.nat (n + 1))
  | some (.imm w) => valWord v = some w
  | some (.cell t) => ∃ ℓ rc m b, v = .loc ℓ ∧ H.cells[ℓ]? = some (.live rc m b) ∧
      UInt64.ofNat b.ctor.tag = (UInt64.ofNat t : Word)
  | none => False

/-- **What a switch's lowering needs of its scrutinee `v`**: `Nat` keys
scrutinise a `Nat` literal, and each alternative's test accepts `v` exactly
when its key is `v`'s. -/
def Dispatches (T : Tables) (H : Own.Heap) (v : Own.RVal) (alts : List (Key.CtorKey × Cfg.Edge)) : Prop :=
  (∀ p ∈ alts, (keyKind T p.1).map KeyKind.isNat = some true → ∃ n, v = .lit (.nat n)) ∧
  ∀ p ∈ alts, ∀ c fs, v.asCtor T.known H = some (c, fs) → (Accepts T H p.1 v ↔ p.1 = c)

/-! ## Words and kinds -/

theorem and_one_toNat (w : Word) : (w &&& 1).toNat = w.toNat % 2 := by
  rw [UInt64.toNat_and, show (UInt64.toNat 1) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem odd_and {w : Word} (h : w.toNat % 2 = 1) : w &&& 1 ≠ 0 := by
  intro e
  have := and_one_toNat w
  rw [e] at this
  simp at this
  omega

theorem even_and {w : Word} (h : w.toNat % 2 = 0) : w &&& 1 = 0 := by
  apply UInt64.toNat_inj.mp
  rw [and_one_toNat, h]
  rfl

theorem ctor0Word_odd (t : Nat) : (ctor0Word t).toNat % 2 = 1 := by
  unfold ctor0Word
  rw [UInt64.toNat_ofNat', Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]
  omega

theorem erasedWord_odd : erasedWord.toNat % 2 = 1 := rfl

theorem natWord_odd {n : Nat} {w : Word} (h : natWord n = some w) : w.toNat % 2 = 1 := by
  rw [natWord_toNat h]; omega

/-- A value that is not a cell has its word. -/
theorem valWord_rel {T : Tables} {P : List Word} {v : Own.RVal} {w : Word} (h : ValRel T P v w)
    (hv : ∀ ℓ, v ≠ .loc ℓ) : valWord v = some w ∧ w.toNat % 2 = 1 := by
  cases v with
  | lit l =>
    cases l with
    | nat n => exact ⟨h, natWord_odd h⟩
    | str _ => exact absurd h id
  | ctor0 c => obtain ⟨rfl, -⟩ := h; exact ⟨rfl, ctor0Word_odd _⟩
  | erased => cases h; exact ⟨rfl, erasedWord_odd⟩
  | loc ℓ => exact absurd rfl (hv ℓ)

theorem keyKind_zero {T : Tables} {k : Key.CtorKey} : keyKind T k = some .zero ↔ T.known.natZero = some k := by
  unfold keyKind
  by_cases h0 : T.known.natZero = some k
  · simp [h0]
  · have h0' : (T.known.natZero == some k) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte, h0, iff_false]
    split
    · simp
    · cases Fir.CtorInfo.ofKey T.ctors k with
      | none => simp
      | some c => simp only [Option.map_some, Option.some.injEq]; split <;> simp

theorem keyKind_succ {T : Tables} {k : Key.CtorKey} (h : keyKind T k = some .succ) :
    T.known.natZero ≠ some k ∧ T.known.natSucc = some k := by
  unfold keyKind at h
  by_cases h0 : T.known.natZero = some k
  · simp [h0] at h
  · have h0' : (T.known.natZero == some k) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at h
    by_cases h1 : T.known.natSucc = some k
    · exact ⟨h0, h1⟩
    · have h1' : (T.known.natSucc == some k) = false := by simpa using h1
      simp only [h1', Bool.false_eq_true, ↓reduceIte] at h
      cases hc : Fir.CtorInfo.ofKey T.ctors k with
      | none => simp [hc] at h
      | some c => simp only [hc, Option.map_some, Option.some.injEq] at h; split at h <;> cases h

theorem keyKind_succ_of {T : Tables} {k : Key.CtorKey} (h0 : T.known.natZero ≠ some k)
    (h1 : T.known.natSucc = some k) : keyKind T k = some .succ := by
  unfold keyKind
  have h0' : (T.known.natZero == some k) = false := by simpa using h0
  simp [h0', h1]

theorem keyKind_imm {T : Tables} {k : Key.CtorKey} {w : Word} (h : keyKind T k = some (.imm w)) :
    ∃ t, w = ctor0Word t := by
  unfold keyKind at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases hc : Fir.CtorInfo.ofKey T.ctors k with
      | none => simp [hc] at h
      | some c =>
        simp only [hc, Option.map_some, Option.some.injEq] at h
        split at h
        · cases h; exact ⟨_, rfl⟩
        · cases h

theorem keyKind_notNat {T : Tables} {k : Key.CtorKey} {kind : KeyKind} (h : keyKind T k = some kind)
    (hn : kind.isNat = false) : T.known.natZero ≠ some k ∧ T.known.natSucc ≠ some k := by
  unfold keyKind at h
  by_cases h0 : T.known.natZero = some k
  · simp [h0] at h; subst h; cases hn
  · by_cases h1 : T.known.natSucc = some k
    · have h0' : (T.known.natZero == some k) = false := by simpa using h0
      simp [h0', h1] at h; subst h; cases hn
    · exact ⟨h0, h1⟩

/-! ## First matches -/

/-- The first test whose immediate is `wx`. -/
def firstMatch (wx : Word) : List (Lir.Arg × PEdge) → Option PEdge
  | [] => none
  | (a, pe) :: rest => if immOf a = some wx then some pe else firstMatch wx rest

theorem chainPick_eq (wx : Word) : ∀ (tests : List (Lir.Arg × PEdge)) (els : PEdge),
    chainPick wx tests els = (firstMatch wx tests).getD els
  | [], _ => rfl
  | (a, pe) :: rest, els => by
    simp only [chainPick, firstMatch]
    split
    · rfl
    · exact chainPick_eq wx rest els

theorem firstMatch_append (wx : Word) : ∀ (l l' : List (Lir.Arg × PEdge)),
    firstMatch wx (l ++ l') = match firstMatch wx l with
      | some pe => some pe
      | none => firstMatch wx l'
  | [], _ => rfl
  | (a, pe) :: rest, l' => by
    simp only [List.cons_append, firstMatch]
    split
    · rfl
    · exact firstMatch_append wx rest l'

/-- A test that matches is taken, default or none. -/
theorem chainOrPick_of_match {wx : Word} {tests : List (Lir.Arg × PEdge)} {pe : PEdge}
    (h : firstMatch wx tests = some pe) (dd : Option PEdge) : chainOrPick wx tests dd = some pe := by
  cases dd with
  | some d => simp [chainOrPick, chainPick_eq, h]
  | none =>
    simp only [chainOrPick]
    cases hu : unsnoc tests with
    | none => rw [unsnoc_none hu] at h; simp [firstMatch] at h
    | some p =>
      obtain ⟨init, a, last⟩ := p
      simp only [Option.some.injEq]
      rw [unsnoc_eq hu, firstMatch_append] at h
      rw [chainPick_eq]
      cases hi : firstMatch wx init with
      | some pe' => rw [hi] at h; simpa using h
      | none =>
        rw [hi] at h
        simp only [firstMatch] at h
        split at h
        · simpa using h
        · simp at h

/-- With no matching test, the default is taken. -/
theorem chainOrPick_dflt {wx : Word} {tests : List (Lir.Arg × PEdge)} (h : firstMatch wx tests = none)
    (d : PEdge) : chainOrPick wx tests (some d) = some d := by
  simp [chainOrPick, chainPick_eq, h]

theorem selectEdge_dflt (c : Key.CtorKey) : ∀ (alts : List (Key.CtorKey × Cfg.Edge)) (d : Option Cfg.Edge),
    Cfg.selectEdge c alts d = match Cfg.selectEdge c alts none with
      | some e => some e
      | none => d
  | [], d => by cases d <;> rfl
  | (k, e) :: rest, d => by
    simp only [Cfg.selectEdge]
    split
    · rfl
    · exact selectEdge_dflt c rest d

/-- The tests of a filtered list of lowered alternatives match where the
keys do. -/
theorem link_tests {R : Key.CtorKey × Cfg.Edge → KeyKind × PEdge → Prop}
    {g : KeyKind × PEdge → Option (Lir.Arg × PEdge)} (hg : ∀ q a pe, g q = some (a, pe) → pe = q.2)
    {c : Key.CtorKey} {wx : Word}
    (hacc : ∀ p q, R p q → ((∃ a pe, g q = some (a, pe) ∧ immOf a = some wx) ↔ p.1 = c)) :
    ∀ {alts : List (Key.CtorKey × Cfg.Edge)} {es : List (KeyKind × PEdge)}, ListRel R alts es →
      (∀ e, Cfg.selectEdge c alts none = some e → ∃ p q, R p q ∧ p.2 = e ∧ firstMatch wx (es.filterMap g) = some q.2) ∧
      (Cfg.selectEdge c alts none = none → firstMatch wx (es.filterMap g) = none)
  | [], [], .nil => ⟨fun e h => by simp [Cfg.selectEdge] at h, fun _ => rfl⟩
  | p :: alts, q :: es, .cons hpq hrest => by
    obtain ⟨ih₁, ih₂⟩ := link_tests hg hacc hrest
    have hq := hacc p q hpq
    by_cases hk : p.1 = c
    · obtain ⟨a, pe, hgq, ha⟩ := hq.2 hk
      have hpe := hg q a pe hgq
      have hsel : Cfg.selectEdge c (p :: alts) none = some p.2 := by
        obtain ⟨k, e⟩ := p
        simp only at hk
        simp [Cfg.selectEdge, hk]
      refine ⟨fun e he => ?_, fun he => by rw [hsel] at he; cases he⟩
      rw [hsel] at he
      cases he
      refine ⟨p, q, hpq, rfl, ?_⟩
      simp only [List.filterMap_cons, hgq, firstMatch, ha, ↓reduceIte, hpe]
    · have hsel : Cfg.selectEdge c (p :: alts) none = Cfg.selectEdge c alts none := by
        obtain ⟨k, e⟩ := p
        simp only at hk
        simp [Cfg.selectEdge, hk]
      have hfm : firstMatch wx ((q :: es).filterMap g) = firstMatch wx (es.filterMap g) := by
        simp only [List.filterMap_cons]
        cases hgq : g q with
        | none => rfl
        | some ap =>
          obtain ⟨a, pe⟩ := ap
          simp only [firstMatch]
          rw [if_neg (fun ha => hk (hq.1 ⟨a, pe, hgq, ha⟩))]
      rw [hsel, hfm]
      exact ⟨ih₁, ih₂⟩

/-- The first alternative of a kind matches where the keys do. -/
theorem link_find {R : Key.CtorKey × Cfg.Edge → KeyKind × PEdge → Prop} {P : KeyKind × PEdge → Bool}
    {c : Key.CtorKey} (hacc : ∀ p q, R p q → (P q = true ↔ p.1 = c)) :
    ∀ {alts : List (Key.CtorKey × Cfg.Edge)} {es : List (KeyKind × PEdge)}, ListRel R alts es →
      (∀ e, Cfg.selectEdge c alts none = some e → ∃ p q, R p q ∧ p.2 = e ∧ (es.find? P).map (·.2) = some q.2) ∧
      (Cfg.selectEdge c alts none = none → (es.find? P).map (·.2) = none)
  | [], [], .nil => ⟨fun e h => by simp [Cfg.selectEdge] at h, fun _ => rfl⟩
  | p :: alts, q :: es, .cons hpq hrest => by
    obtain ⟨ih₁, ih₂⟩ := link_find hacc hrest
    have hq := hacc p q hpq
    by_cases hk : p.1 = c
    · have hP := hq.2 hk
      have hsel : Cfg.selectEdge c (p :: alts) none = some p.2 := by
        obtain ⟨k, e⟩ := p
        simp only at hk
        simp [Cfg.selectEdge, hk]
      refine ⟨fun e he => ?_, fun he => by rw [hsel] at he; cases he⟩
      rw [hsel] at he
      cases he
      exact ⟨p, q, hpq, rfl, by simp [List.find?_cons, hP]⟩
    · have hsel : Cfg.selectEdge c (p :: alts) none = Cfg.selectEdge c alts none := by
        obtain ⟨k, e⟩ := p
        simp only at hk
        simp [Cfg.selectEdge, hk]
      have hP : P q = false := by
        cases h : P q
        · rfl
        · exact absurd (hq.1 h) hk
      rw [hsel, List.find?_cons, hP]
      exact ⟨ih₁, ih₂⟩

end IxCC.Rt.Proof
