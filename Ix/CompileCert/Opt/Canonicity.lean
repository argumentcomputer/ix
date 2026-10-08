import Ix.CompileCert.Opt.Rewrite

/-!
# M7 L3-def: canonicity statements of the definitional passes and the engine

Each pass docstring's *Canonicity* part and the engine's *Confluence* paragraph, restated:

* **C-1, the engine's confluence claim** (`Engine.lean`: "O1, O2, O3, O4 have pairwise disjoint
  patterns … O6 overlaps O1 … On the overlap both give … the same term … O8 and O7 … are disjoint
  from them"): the patterns of the passes (`O1_some`, `O2_pattern`, `O11a_pattern`, `O7_pattern`,
  `O8_pattern`, …) are disjoint where the docstring says so (`O1_O3_disjoint`, …), O1 and O6
  agree where both fire (`O1_O6_agree`), O11a's pattern is inside O2's (`O11a_O2_pattern`: an
  ordered overlap, not a confluent one, as the docstring says), and the engine's result is the
  result of O1, O3 or O4 whenever that pass fires (`engine_of_O1`, `engine_of_O3`, `engine_of_O4`);
* **C-2, the output as a function of the arguments' erasures** ("the output depends on π, π′ …,
  the canonical levels and the arguments, and not on Lean's member order beyond π"): the erasure
  of O1's, O6's, O3's and O4's output is the Ix auxiliary at the shape's levels applied to a
  selection of the arguments' erasures read off the image (`O1_out`, `O6_out`, `O3_out`,
  `O4_out`), so occurrences whose arguments have the same erasure (hashes, binder names and
  `mdata` arbitrary: "does not depend on the hash-consing") get outputs with the same erasure
  (`O1_congr`, …).
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo)
open Ix.CompileCert.Conv
open Ix.Compile.Canon (mkAppN)
open Ix.Compile.Pass.Opt

/-! ## The patterns -/

theorem bool_guard2 : ∀ x y : Bool, ¬ (!x || y) = true → x = true ∧ y = false := by decide

theorem bool_guard3 : ∀ x y z : Bool, ¬ (!x || y || z) = true → x = true ∧ y = false ∧ z = false := by
  decide

/-- O2's pattern: a recursor of a split block with no collapsed class. -/
theorem O2_pattern {recur : Occ → Option Expr} {env : OptEnv} {o : Occ} {e : Expr}
    (h : O2.apply recur env o = some e) :
    ∃ r b, classify o.head = some (.kRec, r) ∧ env.blockOf o.head = some b ∧
      b.change.split = true ∧ b.change.collapse = false := by
  unfold O2.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hsc, -⟩ := oguard h
  have hk' : k = .kRec := by
    cases k
    all_goals first | rfl | exact absurd rfl hk
  subst hk'
  obtain ⟨h1, h2⟩ := bool_guard2 _ _ hsc
  exact ⟨r, b, hc, hb, h1, h2⟩

/-- O8's pattern: `casesOn` of a block with a collapsed class. -/
theorem O8_pattern {env : OptEnv} {o : Occ} {e : Expr} (h : O8.apply env o = some e) :
    ∃ r b, classify o.head = some (.kCasesOn, r) ∧ env.blockOf o.head = some b ∧
      b.change.collapse = true := by
  unfold O8.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨x, -, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hcol, -⟩ := oguard h
  have hk' : k = .kCasesOn := kind_casesOn hk
  subst hk'
  exact ⟨r, b, hc, hb, bnot_false hcol⟩

/-- O7's pattern: `rec`/`recOn` of a collapsed block that is neither split nor evaporating. -/
theorem O7_pattern {env : OptEnv} {o : Occ} {e : Expr} (h : O7.apply env o = some e) :
    ∃ k r b, classify o.head = some (k, r) ∧ (k = .kRec ∨ k = .kRecOn) ∧ env.blockOf o.head = some b ∧
      b.change.collapse = true ∧ b.change.split = false := by
  unfold O7.apply at h
  obtain ⟨⟨k, r⟩, hc, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hk, h⟩ := oguard h
  obtain ⟨b, hb, h⟩ := obind.1 h
  try dsimp only at h
  obtain ⟨hch, -⟩ := oguard h
  obtain ⟨h1, h2, -⟩ := bool_guard3 _ _ _ hch
  exact ⟨k, r, b, hc, kind_rec_or_recOn hk, hb, h1, h2⟩

theorem ebind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    constructor
    · intro h; cases h
    · intro h; obtain ⟨_, h, _⟩ := h; cases h
  | ok a =>
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · intro h; obtain ⟨a', h1, h2⟩ := h; cases h1; exact h2

/-- An `Except` guard `if c then throw e` followed by the rest of a do-block. -/
theorem eguard {c : Prop} [Decidable c] {ε α β : Type} {e₀ : ε} {f : α → Except ε β} {r : Except ε β} {b : β}
    (h : (if c then (throw e₀ >>= f) else r) = .ok b) : ¬ c ∧ r = .ok b := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h
    cases h
  · simp only [hc, ↓reduceIte] at h
    exact ⟨hc, h⟩

theorem epattern {α : Type} {x : Option α} {a : α} (h : O11aM.pattern x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some a' => cases h; rfl

theorem toOption_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | error _ => cases h
  | ok a' => cases h; rfl

/-- O11a's pattern is O2's (an ordered overlap: O11a first, the engine's docstring). -/
theorem O11a_O2_pattern {env : OptEnv} {o : Occ} {e : Expr} (h : O11a.apply env o = some e) :
    ∃ r b, classify o.head = some (.kRec, r) ∧ env.blockOf o.head = some b ∧
      b.change.split = true ∧ b.change.collapse = false := by
  unfold O11a.apply O11a.applyWith at h
  have h' := toOption_some h
  unfold O11a.applyWithE at h'
  obtain ⟨⟨k, r⟩, hc, h'⟩ := ebind.1 h'
  have hc' := epattern hc
  try dsimp only at h'
  obtain ⟨hk, h'⟩ := eguard h'
  obtain ⟨b, hb, h'⟩ := ebind.1 h'
  have hb' := epattern hb
  try dsimp only at h'
  obtain ⟨hsc, -⟩ := eguard h'
  have hk' : k = .kRec := by
    cases k
    all_goals first | rfl | exact absurd rfl hk
  subst hk'
  obtain ⟨h1, h2⟩ := bool_guard2 _ _ hsc
  exact ⟨r, b, hc', hb', h1, h2⟩


/-! ## Disjointness (C-1) -/

theorem O1_O3_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h1 : O1.apply env o = some e)
    (h3 : O3.apply env o = some e') : False := by
  obtain ⟨k, r, _, _, _, hc, -, -, -, -, -, -, -, hbr⟩ := O1_some h1
  obtain ⟨r', _, _, _, _, _, _, hc', -⟩ := O3_some h3
  rw [hc] at hc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc'
  obtain ⟨rfl, -⟩ := hc'
  rcases hbr with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

theorem O1_O4_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h1 : O1.apply env o = some e)
    (h4 : O4.apply env o = some e') : False := by
  obtain ⟨k, r, _, _, _, hc, -, -, -, -, -, -, -, hbr⟩ := O1_some h1
  obtain ⟨k', r', _, _, _, _, _, _, hc', hk', -⟩ := O4_some h4
  rw [hc] at hc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc'
  obtain ⟨rfl, -⟩ := hc'
  rcases hbr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases hk' with h | h | h | h <;> cases h

theorem O3_O4_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h3 : O3.apply env o = some e)
    (h4 : O4.apply env o = some e') : False := by
  obtain ⟨r, _, _, _, _, _, _, hc, -⟩ := O3_some h3
  obtain ⟨k', r', _, _, _, _, _, _, hc', hk', -⟩ := O4_some h4
  rw [hc] at hc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc'
  obtain ⟨rfl, -⟩ := hc'
  rcases hk' with h | h | h | h <;> cases h

theorem O3_O6_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h3 : O3.apply env o = some e)
    (h6 : O6.apply env o = some e') : False := by
  obtain ⟨r, _, _, _, _, _, _, hc, -⟩ := O3_some h3
  obtain ⟨k', r', _, _, _, _, hc', -, -, -, -, -, -, -, hbr⟩ := O6_some h6
  rw [hc] at hc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc'
  obtain ⟨rfl, -⟩ := hc'
  rcases hbr with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

theorem O4_O6_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h4 : O4.apply env o = some e)
    (h6 : O6.apply env o = some e') : False := by
  obtain ⟨k, r, _, _, _, _, _, _, hc, hk, -⟩ := O4_some h4
  obtain ⟨k', r', _, _, _, _, hc', -, -, -, -, -, -, -, hbr⟩ := O6_some h6
  rw [hc] at hc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc'
  obtain ⟨rfl, -⟩ := hc'
  rcases hbr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases hk with h | h | h | h <;> cases h

theorem O1_O2_disjoint {recur : Occ → Option Expr} {env : OptEnv} {o : Occ} {e e' : Expr}
    (h1 : O1.apply env o = some e) (h2 : O2.apply recur env o = some e') : False := by
  obtain ⟨k, r, b, _, _, hc, hb, hperm, -⟩ := O1_some h1
  obtain ⟨r', b', -, hb', hsplit, -⟩ := O2_pattern h2
  rw [hb] at hb'
  cases hb'
  simp only [permutationOnly, hsplit, Bool.not_true, Bool.false_and] at hperm
  cases hperm

theorem O3_O8_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h3 : O3.apply env o = some e)
    (h8 : O8.apply env o = some e') : False := by
  obtain ⟨_, _, b, _, _, _, _, -, -, hb, hcol, -⟩ := O3_some h3
  obtain ⟨_, b', -, hb', hcol'⟩ := O8_pattern h8
  rw [hb] at hb'
  cases hb'
  rw [hcol] at hcol'
  cases hcol'

theorem O1_O7_disjoint {env : OptEnv} {o : Occ} {e e' : Expr} (h1 : O1.apply env o = some e)
    (h7 : O7.apply env o = some e') : False := by
  obtain ⟨_, _, b, _, _, -, hb, hperm, -⟩ := O1_some h1
  obtain ⟨_, _, b', -, -, hb', hcol, -⟩ := O7_pattern h7
  rw [hb] at hb'
  cases hb'
  simp only [permutationOnly, hcol, Bool.not_true, Bool.and_false, Bool.false_and] at hperm
  cases hperm

theorem O2_O7_disjoint {recur : Occ → Option Expr} {env : OptEnv} {o : Occ} {e e' : Expr}
    (h2 : O2.apply recur env o = some e) (h7 : O7.apply env o = some e') : False := by
  obtain ⟨_, b, -, hb, -, hcol⟩ := O2_pattern h2
  obtain ⟨_, _, b', -, -, hb', hcol', -⟩ := O7_pattern h7
  rw [hb] at hb'
  cases hb'
  rw [hcol] at hcol'
  cases hcol'

/-! ## Agreement on the overlap (C-1) -/

/-- **O1 and O6 agree** where both fire (the engine's "O6 overlaps O1 … both give the same
term"). -/
theorem O1_O6_agree {env : OptEnv} {o : Occ} {e e' : Expr} (h1 : O1.apply env o = some e)
    (h6 : O6.apply env o = some e') : e = e' := by
  obtain ⟨k, r, b, s, ls, hc, hb, -, hs, -, -, -, hls, hbr⟩ := O1_some h1
  obtain ⟨k', r', b', s', ls', ms6, hc', hb', hs', -, -, -, hls', hms6, hbr'⟩ := O6_some h6
  rw [hc] at hc'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc'
  obtain ⟨rfl, rfl⟩ := hc'
  rw [hb] at hb'
  cases hb'
  rw [hs] at hs'
  cases hs'
  rw [hls] at hls'
  cases hls'
  rcases hbr with ⟨rfl, ms', mins', hms, hmins, rfl⟩ | ⟨rfl, ixRecOn, ms', mins', hix, -, hms, hmins, rfl⟩
  · rcases hbr' with ⟨-, mins6, hmins6, rfl⟩ | ⟨h, -⟩
    · rw [hms] at hms6
      cases hms6
      rw [hmins] at hmins6
      cases hmins6
      rfl
    · cases h
  · rcases hbr' with ⟨h, -⟩ | ⟨-, ixRecOn6, mins6, hix6, -, hmins6, rfl⟩
    · cases h
    · rw [hms] at hms6
      cases hms6
      rw [hmins] at hmins6
      cases hmins6
      rw [hix] at hix6
      cases hix6
      rfl

/-! ## The engine's result (C-1) -/

theorem engine_of_O1 {env : OptEnv} {fuel : Nat} {o : Occ} {e : Expr} (h1 : O1.apply env o = some e) :
    engineN (fuel + 1) env o = some ("O1", e) := by
  simp only [engineN, passes, List.cons_append, List.findSome?, h1, Option.map_some]

theorem engine_of_O3 {env : OptEnv} {fuel : Nat} {o : Occ} {e : Expr} (h3 : O3.apply env o = some e) :
    engineN (fuel + 1) env o = some ("O3", e) := by
  have n1 : O1.apply env o = none := by
    cases h : O1.apply env o with
    | none => rfl
    | some e1 => exact (O1_O3_disjoint h h3).elim
  have n11 : O11a.apply env o = none := by
    cases h : O11a.apply env o with
    | none => rfl
    | some e1 =>
      exfalso
      obtain ⟨r, _, _, _, _, _, _, hc, -⟩ := O3_some h3
      obtain ⟨r', _, hc', -⟩ := O11a_O2_pattern h
      rw [hc] at hc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨hk0, -⟩ := hc'
      cases hk0
  have n2 : O2.apply (fun o' => (engineN fuel env o').map (·.2)) env o = none := by
    cases h : O2.apply (fun o' => (engineN fuel env o').map (·.2)) env o with
    | none => rfl
    | some e1 =>
      exfalso
      obtain ⟨r, _, _, _, _, _, _, hc, -⟩ := O3_some h3
      obtain ⟨r', _, hc', -⟩ := O2_pattern h
      rw [hc] at hc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨hk0, -⟩ := hc'
      cases hk0
  simp only [engineN, passes, List.cons_append, List.findSome?, n1, n11, n2, h3, Option.map_none,
    Option.map_some]

theorem engine_of_O4 {env : OptEnv} {fuel : Nat} {o : Occ} {e : Expr} (h4 : O4.apply env o = some e) :
    engineN (fuel + 1) env o = some ("O4", e) := by
  obtain ⟨k, r, _, _, _, _, _, _, hc, hk, -⟩ := O4_some h4
  have n1 : O1.apply env o = none := by
    cases h : O1.apply env o with
    | none => rfl
    | some e1 => exact (O1_O4_disjoint h h4).elim
  have n3 : O3.apply env o = none := by
    cases h : O3.apply env o with
    | none => rfl
    | some e1 => exact (O3_O4_disjoint h h4).elim
  have n11 : O11a.apply env o = none := by
    cases h : O11a.apply env o with
    | none => rfl
    | some e1 =>
      exfalso
      obtain ⟨r', _, hc', -⟩ := O11a_O2_pattern h
      rw [hc] at hc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨rfl, -⟩ := hc'
      rcases hk with h | h | h | h <;> cases h
  have n2 : O2.apply (fun o' => (engineN fuel env o').map (·.2)) env o = none := by
    cases h : O2.apply (fun o' => (engineN fuel env o').map (·.2)) env o with
    | none => rfl
    | some e1 =>
      exfalso
      obtain ⟨r', _, hc', -⟩ := O2_pattern h
      rw [hc] at hc'
      simp only [Option.some.injEq, Prod.mk.injEq] at hc'
      obtain ⟨rfl, -⟩ := hc'
      rcases hk with h | h | h | h <;> cases h
  simp only [engineN, passes, List.cons_append, List.findSome?, n1, n11, n2, n3, h4, Option.map_none,
    Option.map_some]

/-! ## The output as a function of the arguments' erasures (C-2) -/

/-- O1's output: the Ix recursor (or `recOn`) at the shape's levels, applied to the shape's
selection of the arguments' erasures, then the rest. -/
theorem O1_out {env : OptEnv} {o : Occ} {e : Expr} (h : O1.apply env o = some e) :
    ∃ (c : Name) (ls : Array Level) (idx : List Nat) (n : Nat),
      er e = Tm.appN (.const c ls) (idx.map (argT o.args) ++
        (List.range (o.args.size - n)).map (fun k => argT o.args (n + k))) := by
  obtain ⟨k, r, b, s, ls, -, -, -, -, -, -, hn, -, hbr⟩ := O1_some h
  have har : s.arity = s.np + s.nm + s.nmin + s.ni + 1 := rfl
  rcases hbr with ⟨-, ms', mins', hms, hmins, rfl⟩ | ⟨-, ixRecOn, ms', mins', -, -, hms, hmins, rfl⟩
  · obtain ⟨hms1, -⟩ := pick_extract (by omega) hms
    obtain ⟨hmi1, -⟩ := pick_extract (by omega) hmins
    refine ⟨s.ixRec, ls, shapeIdx s, s.arity, ?_⟩
    have e1 := extract_map o.args (i := 0) (j := s.np) (by omega)
    have e4 := extract_map o.args (i := s.np + s.nm + s.nmin) (j := s.arity) hn
    have e5 := extract_map o.args (i := s.arity) (j := o.args.size) (Nat.le_refl _)
    rw [er_mkAppN, er_mkConst]
    congr 1
    simp only [Array.toList_append, List.map_append]
    rw [e1, hms1, hmi1, e4, e5, Array.toList_filterMap]
    simp only [shapeIdx, selMinors, List.map_append, List.map_map, Nat.sub_zero, Nat.zero_add]
    rw [show s.arity - (s.np + s.nm + s.nmin) = s.ni + 1 by omega]
    try rfl
  · obtain ⟨hms1, -⟩ := pick_extract (by omega) hms
    obtain ⟨hmi1, -⟩ := pick_extract hn hmins
    refine ⟨ixRecOn, ls, recOnOutIdx s, s.arity, ?_⟩
    have e1 := extract_map o.args (i := 0) (j := s.np) (by omega)
    have e3 := extract_map o.args (i := s.np + s.nm) (j := s.np + s.nm + s.ni + 1) (by omega)
    have e5 := extract_map o.args (i := s.arity) (j := o.args.size) (Nat.le_refl _)
    rw [er_mkAppN, er_mkConst]
    congr 1
    simp only [Array.toList_append, List.map_append]
    rw [e1, hms1, e3, hmi1, e5, Array.toList_filterMap]
    simp only [recOnOutIdx, selMinors, List.map_append, List.map_map, Nat.sub_zero, Nat.zero_add]
    rw [show s.np + s.nm + s.ni + 1 - (s.np + s.nm) = s.ni + 1 by omega]
    try rfl

/-- **Erasure congruence** (C-2): two occurrences of one head at one level with arguments of the
same erasure get outputs of the same erasure from O1 (the hashes, binder names and `mdata` of the
arguments are not read). -/
theorem argT_congr {a a' : Array Expr} (h : a.toList.map er = a'.toList.map er) : argT a = argT a' := by
  funext i
  rw [← gL_args a, ← gL_args a', h]

/-! ## O11a selection and positive fuel -/

/-- A split-block O11a success cannot overlap the permutation-only O1 pass. -/
theorem O1_O11a_disjoint {env : OptEnv} {o : Occ} {e e' : Expr}
    (h1 : O1.apply env o = some e) (h11 : O11a.apply env o = some e') : False := by
  obtain ⟨_, _, b, _, _, _, hb, hperm, _⟩ := O1_some h1
  obtain ⟨_, b', _, hb', hsplit, _⟩ := O11a_O2_pattern h11
  rw [hb] at hb'
  cases hb'
  simp only [permutationOnly, hsplit, Bool.not_true, Bool.false_and] at hperm
  cases hperm

/-- O11a is selected at every positive fuel. Its result needs no relocated recursive call. -/
theorem engine_of_O11a {env : OptEnv} {fuel : Nat} {o : Occ} {e : Expr}
    (h11 : O11a.apply env o = some e) : engineN (fuel + 1) env o = some ("O11a", e) := by
  have h1 : O1.apply env o = none := by
    cases h : O1.apply env o with
    | none => rfl
    | some e' => exact False.elim (O1_O11a_disjoint h h11)
  simp only [engineN, passes, List.cons_append, List.findSome?, h1, Option.map_none,
    h11, Option.map_some]

/-- Positive fuel changes do not affect an occurrence selected by O11a. This is a restricted
fuel-independence lemma, not a discharge of the O2 relocation-depth bound. -/
theorem engineN_O11a_fuel_eq {env : OptEnv} {o : Occ} {e : Expr}
    (h11 : O11a.apply env o = some e) (fuel fuel' : Nat) :
    engineN (fuel + 1) env o = engineN (fuel' + 1) env o := by
  rw [engine_of_O11a h11, engine_of_O11a h11]

/-- The shipped fuel-64 engine returns the O11a result without emitting auxiliary constants. -/
theorem engineFull_of_O11a {env : OptEnv} {o : Occ} {e : Expr}
    (h11 : O11a.apply env o = some e) : engineFull env o = some ("O11a", e, #[]) := by
  have h : engine env o = some ("O11a", e) := engine_of_O11a (fuel := 63) h11
  unfold engineFull
  rw [h]

end Ix.CompileCert.Opt
