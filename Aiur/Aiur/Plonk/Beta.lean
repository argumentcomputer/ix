import Aiur.Plonk.Scs
import Mathlib.Algebra.Field.ZMod
import Std.Data.HashMap
import Std.Data.HashSet
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Gates that force `β` to be a fixed function of `γ`

The second lookup challenge `β` is computed in-circuit from the commitment
challenge `γ` (BLAKE3, `BetaGadget.lean`). Soundness needs only that the
emitted gates leave no freedom: every satisfying assignment has
`w β = B (w γ)` for one function `B : ZMod p → ZMod p`. The gadget is a list of
`Step`s, each contributing gates:

* `lin g`: the gate `g` with `qO ≠ 0` and operands `a`, `b` already
  determined, so `w c = −(qL·a + qR·b + qM·a·b + qC)/qO` is determined;
* `bits x bs accs canon`: the bit wires `bs` (most significant first) of the
  determined wire `x`: one booleanity gate per bit, a Horner chain
  `acc' = 2·acc + b` ending at `x`, and, when `canon = some ps`, a comparison
  chain forcing `Σ 2^i·bᵢ ≤ p − 1` as natural numbers. With `2^n ≤ p`, or
  with the comparison, the decomposition is the canonical one: each bit is
  `natBits n (w x).val` (`bits_canonical`). Without it a prover could choose
  the bits of `w x + p` when that is below `2^n`.

`checkAll` decides the structural conditions (which wires are determined,
`qO ≠ 0`, the bit-width side conditions) without looking at values;
`evalAll` computes the determined values. `beta_functional`: if
`betaOk steps γ β` holds and `w` satisfies the gadget's gates, then
`w β = betaFn steps γ β (w γ)`.
-/

namespace Aiur.Plonk.Beta

/-! ## Bits as natural numbers -/

/-- The bits of `N` at positions `m − 1, …, 0`, most significant first. -/
def natBits (m N : Nat) : List Nat := (List.range m).reverse.map fun j => N / 2 ^ j % 2

/-- The value of a most-significant-first digit list in base 2. -/
def hN : List Nat → Nat
  | [] => 0
  | x :: t => x * 2 ^ t.length + hN t

def hF {F : Type} [CommRing F] : List F → F
  | [] => 0
  | x :: t => x * 2 ^ t.length + hF t

theorem natBits_succ (m N : Nat) : natBits (m + 1) N = (N / 2 ^ m % 2) :: natBits m N := by
  simp [natBits, List.range_succ, List.reverse_append]

@[simp] theorem length_natBits (m N : Nat) : (natBits m N).length = m := by simp [natBits]

theorem hN_natBits (m N : Nat) : hN (natBits m N) = N % 2 ^ m := by
  induction m with
  | zero => simp [natBits, hN, Nat.mod_one]
  | succ m ih =>
      rw [natBits_succ, hN, length_natBits, ih, Nat.mod_pow_succ]
      ring

theorem natBits_congr {m A B : Nat} (h : ∀ j < m, A / 2 ^ j % 2 = B / 2 ^ j % 2) :
    natBits m A = natBits m B := by
  simp only [natBits]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_reverse, List.mem_range] at hj
  exact h j hj

theorem div_pow_mod_two_add (h x m j : Nat) (hj : j < m) :
    (h + x * 2 ^ m) / 2 ^ j % 2 = h / 2 ^ j % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = j + 1 + k := ⟨m - j - 1, by omega⟩
  have e : x * 2 ^ (j + 1 + k) = (2 * (x * 2 ^ k)) * 2 ^ j := by
    rw [pow_add, pow_add, pow_one]; ring
  rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_left]

def IsBits (l : List Nat) : Prop := ∀ x ∈ l, x ≤ 1

theorem hN_lt : ∀ {l : List Nat}, IsBits l → hN l < 2 ^ l.length
  | [], _ => by simp [hN]
  | x :: t, h => by
      have hx : x ≤ 1 := h x List.mem_cons_self
      have ht := hN_lt (l := t) fun y hy => h y (List.mem_cons_of_mem _ hy)
      have : x * 2 ^ t.length ≤ 1 * 2 ^ t.length := Nat.mul_le_mul_right _ hx
      simp only [hN, List.length_cons, pow_succ]
      generalize 2 ^ t.length = P at *
      omega

theorem natBits_hN : ∀ {l : List Nat}, IsBits l → natBits l.length (hN l) = l
  | [], _ => by simp [natBits]
  | x :: t, h => by
      have hx : x ≤ 1 := h x List.mem_cons_self
      have ht' : IsBits t := fun y hy => h y (List.mem_cons_of_mem _ hy)
      have ht := hN_lt ht'
      rw [List.length_cons, natBits_succ, hN]
      congr 1
      · rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt ht, Nat.add_zero,
          Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.add_comm, natBits_congr (B := hN t) fun j hj => div_pow_mod_two_add _ _ _ _ hj]
        exact natBits_hN ht'

theorem hN_cast {F : Type} [CommRing F] :
    ∀ l : List Nat, ((hN l : Nat) : F) = hF (l.map (Nat.cast : Nat → F))
  | [] => by simp [hN, hF]
  | x :: t => by simp [hN, hF, hN_cast t]

theorem foldl_horner {F : Type} [CommRing F] : ∀ (vs : List F) (a : F),
    vs.foldl (fun a v => 2 * a + v) a = a * 2 ^ vs.length + hF vs
  | [], a => by simp [hF]
  | v :: vs, a => by
      rw [List.foldl_cons, foldl_horner vs, hF, List.length_cons, pow_succ]
      ring

/-! ## The gates of a bit decomposition -/

def boolGate {F : Type} [Ring F] (b : Nat) : Gate F := ⟨b, b, b, -1, 0, 0, 1, 0⟩

/-- `x = Σ` of the bits `prev :: rest` (most significant first) by
`acc' = 2·acc + b`; the intermediate wires are taken from `accs`. -/
def hornerGates {F : Type} [Ring F] (x : Nat) : Nat → List Nat → List Nat → List (Gate F)
  | prev, [], _ => [⟨prev, prev, x, 1, 0, -1, 0, 0⟩]
  | prev, [b], _ => [⟨prev, b, x, 2, 1, -1, 0, 0⟩]
  | prev, b :: b' :: rest, accs =>
      ⟨prev, b, accs.headD 0, 2, 1, -1, 0, 0⟩ :: hornerGates x (accs.headD 0) (b' :: rest) accs.tail

/-- The comparison of the bits `bs` with the constant bits `ks` (both most
significant first). `p` is the wire holding "every earlier bit equals the
constant's", `none` while that is the constant `1`. Where `k = 1` the flag
becomes `p·b` (a fresh wire from `ps`); where `k = 0` the gate `p·b = 0`
forbids a `1` while the prefix is equal. -/
def canonGates {F : Type} [Ring F] : Option Nat → List Nat → List Nat → List Nat → List (Gate F)
  | p, b :: bs, k :: ks, ps =>
      if k = 1 then
        match p with
        | none => canonGates (some b) bs ks ps
        | some pw => ⟨pw, b, ps.headD 0, 0, 0, -1, 1, 0⟩ :: canonGates (some (ps.headD 0)) bs ks ps.tail
      else
        (match p with
          | none => (⟨b, b, b, 1, 0, 0, 0, 0⟩ : Gate F)
          | some pw => ⟨pw, b, b, 0, 0, 0, 1, 0⟩) :: canonGates p bs ks ps
  | _, _, _, _ => []

section FieldLemmas

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem bool_of_boolGate (w : Nat → F) {b : Nat} (h : (boolGate b).Holds w) : w b = 0 ∨ w b = 1 := by
  simp only [boolGate, Gate.Holds] at h
  have : w b * (w b - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact .inl h0
  · exact .inr (sub_eq_zero.mp h1)

omit [DecidableEq F] in
theorem horner_sound (w : Nat → F) {x : Nat} : ∀ (rest : List Nat) (prev : Nat) (accs : List Nat),
    (∀ g ∈ hornerGates x prev rest accs, g.Holds w) →
      w x = (rest.map w).foldl (fun a v => 2 * a + v) (w prev)
  | [], prev, _, h => by
      have := h ⟨prev, prev, x, 1, 0, -1, 0, 0⟩ (by simp [hornerGates])
      simp only [Gate.Holds] at this
      simp only [List.map_nil, List.foldl_nil]
      linear_combination -this
  | [b], prev, _, h => by
      have := h ⟨prev, b, x, 2, 1, -1, 0, 0⟩ (by simp [hornerGates])
      simp only [Gate.Holds] at this
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      linear_combination -this
  | b :: b' :: rest, prev, accs, h => by
      have h0 := h ⟨prev, b, accs.headD 0, 2, 1, -1, 0, 0⟩ (by simp [hornerGates])
      have ih := horner_sound w (b' :: rest) (accs.headD 0) accs.tail fun g hg =>
        h g (by simp only [hornerGates, List.mem_cons]; exact .inr hg)
      simp only [Gate.Holds] at h0
      have e : w (accs.headD 0) = 2 * w prev + w b := by linear_combination -h0
      rw [ih, e]
      simp only [List.map_cons, List.foldl_cons]

/-- `1` when `x = 1`, else `0`: the bit a boolean wire holds. -/
def bitOf (x : F) : Nat := if x = 1 then 1 else 0

theorem bitOf_cast {x : F} (h : x = 0 ∨ x = 1) : ((bitOf x : Nat) : F) = x := by
  rcases h with rfl | rfl <;> simp [bitOf]

theorem isBits_bitOf (w : Nat → F) (l : List Nat) : IsBits (l.map fun b => bitOf (w b)) := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨_, _, rfl⟩ := hy
  unfold bitOf; split <;> omega

omit [DecidableEq F] in
def flagVal (w : Nat → F) (p : Option Nat) : F := match p with
  | none => 1
  | some pw => w pw

theorem canon_le (w : Nat → F) : ∀ (bs ks : List Nat) (p : Option Nat) (ps : List Nat), ks.length = bs.length →
    (∀ k ∈ ks, k ≤ 1) → (∀ b ∈ bs, w b = 0 ∨ w b = 1) →
    (∀ g ∈ canonGates p bs ks ps, g.Holds w) → flagVal w p = 1 →
      hN (bs.map fun b => bitOf (w b)) ≤ hN ks
  | [], ks, _, _, hl, _, _, _, _ => by
      cases ks with
      | nil => simp [hN]
      | cons _ _ => simp at hl
  | _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl
  | b :: bs, k :: ks, p, ps, hl, hk, hb, h, hp => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hk' : ∀ k ∈ ks, k ≤ 1 := fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')
      have hb' : ∀ b ∈ bs, w b = 0 ∨ w b = 1 := fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')
      have hbb := hb b List.mem_cons_self
      have tail_lt := hN_lt (isBits_bitOf w bs)
      simp only [List.length_map] at tail_lt
      simp only [List.map_cons, hN, List.length_map, hl]
      by_cases k1 : k = 1
      · subst k1
        have finish : ∀ (p' : Option Nat) (ps' : List Nat), (∀ g ∈ canonGates p' bs ks ps', g.Holds w) →
            flagVal w p' = w b →
            bitOf (w b) * 2 ^ bs.length + hN (bs.map fun b => bitOf (w b)) ≤ 1 * 2 ^ bs.length + hN ks := by
          intro p' ps' hg' hv
          rcases hbb with h0 | h1
          · have e : bitOf (w b) = 0 := by simp [bitOf, h0]
            rw [e]; omega
          · have e : bitOf (w b) = 1 := by simp [bitOf, h1]
            have ih := canon_le w bs ks p' ps' hl hk' hb' hg' (hv.trans h1)
            rw [e]; omega
        cases p with
        | none => exact finish (some b) ps (fun g hg => h g hg) rfl
        | some pw =>
            have h0 := h ⟨pw, b, ps.headD 0, 0, 0, -1, 1, 0⟩ List.mem_cons_self
            refine finish (some (ps.headD 0)) ps.tail (fun g hg => h g (List.mem_cons_of_mem _ hg)) ?_
            simp only [Gate.Holds, flagVal] at h0 hp ⊢
            rw [hp] at h0
            linear_combination -h0
      · have k0 : k = 0 := by have := hk k List.mem_cons_self; omega
        subst k0
        have hz : w b = 0 := by
          cases p with
          | none =>
              have h0 := h ⟨b, b, b, 1, 0, 0, 0, 0⟩ List.mem_cons_self
              simp only [Gate.Holds] at h0
              linear_combination h0
          | some pw =>
              have h0 := h ⟨pw, b, b, 0, 0, 0, 1, 0⟩ List.mem_cons_self
              simp only [Gate.Holds, flagVal] at h0 hp
              rw [hp] at h0
              linear_combination h0
        have ih := canon_le w bs ks p ps hl hk' hb' (fun g hg => h g (List.mem_cons_of_mem _ hg)) hp
        have e : bitOf (w b) = 0 := by simp [bitOf, hz]
        rw [e]; omega

end FieldLemmas

/-! ## Steps, the structural check and the evaluator -/

inductive Step (F : Type) where
  | lin (g : Gate F)
  | bits (x : Nat) (bs accs : List Nat) (canon : Option (List Nat))

def bitsWidthOk (p n : Nat) : Option (List Nat) → Bool
  | none => decide (2 ^ n ≤ p)
  | some _ => decide (p ≤ 2 ^ n)

def Step.gates {p : Nat} : Step (ZMod p) → List (Gate (ZMod p))
  | .lin g => [g]
  | .bits x bs accs canon =>
      bs.map boolGate ++
        (match bs with
          | [] => []
          | b :: rest => hornerGates x b rest accs) ++
        (match canon with
          | none => []
          | some ps => canonGates none bs (natBits bs.length (p - 1)) ps)

/-- The structural conditions of a step; `D` is the set of determined wires. -/
def Step.check {p : Nat} (D : Std.HashSet Nat) : Step (ZMod p) → Option (Std.HashSet Nat)
  | .lin g => if D.contains g.a && D.contains g.b && g.qO != 0 then some (D.insert g.c) else none
  | .bits x bs _ canon =>
      if D.contains x && !bs.isEmpty && bitsWidthOk p bs.length canon then
        some (bs.foldl (fun D b => D.insert b) D)
      else none

def checkAll {p : Nat} : Std.HashSet Nat → List (Step (ZMod p)) → Option (Std.HashSet Nat)
  | D, [] => some D
  | D, s :: ss =>
      match s.check D with
      | none => none
      | some D' => checkAll D' ss

def gadgetGates {p : Nat} (ss : List (Step (ZMod p))) : List (Gate (ZMod p)) :=
  ss.flatMap Step.gates

def betaOk {p : Nat} (ss : List (Step (ZMod p))) (γw βw : Nat) : Bool :=
  match checkAll (({} : Std.HashSet Nat).insert γw) ss with
  | some D => D.contains βw
  | none => false

section Prime

variable {p : Nat} [Fact (Nat.Prime p)]

def Step.eval (env : Std.HashMap Nat (ZMod p)) : Step (ZMod p) → Std.HashMap Nat (ZMod p)
  | .lin g =>
      let va := env.getD g.a 0
      let vb := env.getD g.b 0
      env.insert g.c (-(g.qL * va + g.qR * vb + g.qM * (va * vb) + g.qC) / g.qO)
  | .bits x bs _ _ =>
      (bs.zip ((natBits bs.length (env.getD x 0).val).map (Nat.cast : Nat → ZMod p))).foldl
        (fun e pair => e.insert pair.1 pair.2) env

def evalAll : Std.HashMap Nat (ZMod p) → List (Step (ZMod p)) → Std.HashMap Nat (ZMod p)
  | e, [] => e
  | e, s :: ss => evalAll (s.eval e) ss

def Agree (w : Nat → ZMod p) (D : Std.HashSet Nat) (env : Std.HashMap Nat (ZMod p)) : Prop :=
  ∀ x, D.contains x = true → w x = env.getD x 0

theorem agree_insert (w : Nat → ZMod p) {D : Std.HashSet Nat} {env : Std.HashMap Nat (ZMod p)}
    (h : Agree w D env) {k : Nat} {v : ZMod p} (hk : w k = v) :
    Agree w (D.insert k) (env.insert k v) := by
  intro x hx
  rw [Std.HashSet.contains_insert] at hx
  rw [Std.HashMap.getD_insert]
  by_cases e : k = x
  · subst e; simp [hk]
  · have : (k == x) = false := by simp [e]
    rw [this, Bool.false_or] at hx
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact h x hx

theorem agree_fold (w : Nat → ZMod p) :
    ∀ (ps : List (Nat × ZMod p)) (D : Std.HashSet Nat) (env : Std.HashMap Nat (ZMod p)),
    Agree w D env → (∀ pair ∈ ps, w pair.1 = pair.2) →
      Agree w (ps.foldl (fun D pair => D.insert pair.1) D) (ps.foldl (fun e pair => e.insert pair.1 pair.2) env)
  | [], _, _, h, _ => h
  | pair :: ps, D, env, h, hp => by
      simp only [List.foldl_cons]
      exact agree_fold w ps _ _ (agree_insert w h (hp pair List.mem_cons_self))
        fun q hq => hp q (List.mem_cons_of_mem _ hq)

theorem mem_zip_map_self {α β : Type} (f : α → β) : ∀ (l : List α) (pair : α × β),
    pair ∈ l.zip (l.map f) → pair.2 = f pair.1
  | [], _, h => by simp at h
  | _ :: l, pair, h => by
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact mem_zip_map_self f l pair h

/-- A checked decomposition step holds exactly the canonical bits of `w x`. -/
theorem bits_canonical (w : Nat → ZMod p) {x : Nat} {bs accs : List Nat} {canon : Option (List Nat)}
    (hw : bitsWidthOk p bs.length canon = true) (hne : bs ≠ [])
    (h : ∀ g ∈ (Step.bits (F := ZMod p) x bs accs canon).gates, g.Holds w) :
    natBits bs.length (w x).val = bs.map fun b => bitOf (w b) := by
  have hb : ∀ b ∈ bs, w b = 0 ∨ w b = 1 := fun b hb =>
    bool_of_boolGate w (h _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hb))))
  obtain ⟨b0, rest, rfl⟩ : ∃ b0 rest, bs = b0 :: rest := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b0 rest => exact ⟨b0, rest, rfl⟩
  have hx := horner_sound w rest b0 accs fun g hg =>
    h g (List.mem_append_left _ (List.mem_append_right _ hg))
  rw [foldl_horner, List.length_map] at hx
  set bv := (b0 :: rest).map fun b => bitOf (w b) with hbv
  have hcast : w x = ((hN bv : Nat) : ZMod p) := by
    rw [hN_cast, hbv, List.map_map, hx]
    have : ((b0 :: rest).map ((Nat.cast : Nat → ZMod p) ∘ fun b => bitOf (w b))) = (b0 :: rest).map w :=
      List.map_congr_left fun b hb' => bitOf_cast (hb b hb')
    rw [this]
    simp [hF]
  have hbits : IsBits bv := isBits_bitOf w _
  have hlen : bv.length = (b0 :: rest).length := by simp [hbv]
  have hlt : hN bv < p := by
    cases canon with
    | none =>
        have h2 : 2 ^ (b0 :: rest).length ≤ p := of_decide_eq_true hw
        have := hN_lt hbits
        rw [hlen] at this
        omega
    | some ps =>
        have h2 : p ≤ 2 ^ (b0 :: rest).length := of_decide_eq_true hw
        have hle := canon_le w (b0 :: rest) (natBits (b0 :: rest).length (p - 1)) none ps
          (length_natBits _ _)
          (fun k hk => by
            simp only [natBits, List.mem_map] at hk
            obtain ⟨_, _, rfl⟩ := hk
            omega)
          hb (fun g hg => h g (List.mem_append_right _ hg)) rfl
        have hp : 0 < p := (Fact.out : Nat.Prime p).pos
        rw [← hbv, hN_natBits, Nat.mod_eq_of_lt (by omega)] at hle
        omega
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ← hlen]
  exact natBits_hN hbits

theorem step_sound (w : Nat → ZMod p) {s : Step (ZMod p)} {D D' : Std.HashSet Nat}
    {env : Std.HashMap Nat (ZMod p)}
    (hc : s.check D = some D') (h : ∀ g ∈ s.gates, g.Holds w) (ha : Agree w D env) :
    Agree w D' (s.eval env) := by
  cases s with
  | lin g =>
      simp only [Step.check, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      split at hc
      · rename_i hg
        obtain ⟨⟨hA, hB⟩, hO⟩ := hg
        cases hc
        apply agree_insert w ha
        have hg := h g (by simp [Step.gates])
        simp only [Gate.Holds] at hg
        rw [← ha _ hA, ← ha _ hB, eq_div_iff hO]
        linear_combination hg
      · cases hc
  | bits x bs accs canon =>
      simp only [Step.check, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
      split at hc
      · rename_i hg
        obtain ⟨⟨hX, hne⟩, hw⟩ := hg
        cases hc
        have can := bits_canonical w hw hne h
        simp only [Step.eval]
        rw [← ha _ hX, can, List.map_map]
        have hfold : bs.foldl (fun D b => D.insert b) D =
            (bs.zip (bs.map ((Nat.cast : Nat → ZMod p) ∘ fun b => bitOf (w b)))).foldl (fun D pair => D.insert pair.1) D := by
          rw [show (bs.zip (bs.map ((Nat.cast : Nat → ZMod p) ∘ fun b => bitOf (w b)))).foldl
              (fun D pair => D.insert pair.1) D =
              ((bs.zip (bs.map ((Nat.cast : Nat → ZMod p) ∘ fun b => bitOf (w b)))).map Prod.fst).foldl
              (fun D b => D.insert b) D from List.foldl_map.symm, List.map_fst_zip (by simp)]
        rw [hfold]
        apply agree_fold w _ _ _ ha
        intro pair hp
        rw [mem_zip_map_self _ bs pair hp]
        have hb : ∀ b ∈ bs, w b = 0 ∨ w b = 1 := fun b hb =>
          bool_of_boolGate w (h _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hb))))
        have hp1 : pair.1 ∈ bs := (List.of_mem_zip hp).1
        exact (bitOf_cast (hb _ hp1)).symm
      · cases hc

theorem checkAll_sound (w : Nat → ZMod p) :
    ∀ (ss : List (Step (ZMod p))) (D D' : Std.HashSet Nat) (env : Std.HashMap Nat (ZMod p)),
    checkAll D ss = some D' → (∀ g ∈ gadgetGates ss, g.Holds w) → Agree w D env → Agree w D' (evalAll env ss)
  | [], _, _, _, hc, _, ha => by cases hc; exact ha
  | s :: ss, D, D', env, hc, h, ha => by
      simp only [checkAll] at hc
      split at hc
      · cases hc
      · rename_i D1 h1
        exact checkAll_sound w ss D1 D' _ hc (fun g hg => h g (by
            simp only [gadgetGates, List.flatMap_cons, List.mem_append]; exact .inr hg))
          (step_sound w h1 (fun g hg => h g (by
            simp only [gadgetGates, List.flatMap_cons, List.mem_append]; exact .inl hg)) ha)

/-! ## The gadget's function -/

/-- The value the checked gadget forces on `βw` when `γw` holds `γ`. -/
def betaFn (ss : List (Step (ZMod p))) (γw βw : Nat) (γ : ZMod p) : ZMod p :=
  (evalAll (({} : Std.HashMap Nat (ZMod p)).insert γw γ) ss).getD βw 0

theorem beta_functional (w : Nat → ZMod p) {ss : List (Step (ZMod p))} {γw βw : Nat}
    (ok : betaOk ss γw βw = true) (sat : ∀ g ∈ gadgetGates ss, g.Holds w) :
    w βw = betaFn ss γw βw (w γw) := by
  unfold betaOk at ok
  split at ok
  · rename_i D hD
    have h0 : Agree w (({} : Std.HashSet Nat).insert γw) (({} : Std.HashMap Nat (ZMod p)).insert γw (w γw)) :=
      agree_insert w (fun _ hx => by simp at hx) rfl
    exact checkAll_sound w ss _ D _ hD sat h0 βw ok
  · cases ok

end Prime

end Aiur.Plonk.Beta
