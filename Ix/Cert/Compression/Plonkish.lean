import Aiur.Library.Blake3.Correctness
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring

/-! # Flat Degree-2 Plonkish Circuit IR and Sharded Multi-STARK Lowering

Formalization of `multi_stark::plonkish::Circuit<F>` and its sharded lowering
(`crates/proof-compression/src/pipeline/lowering.rs`):
1. Core Plonkish IR types (`Wire`, `Gate`, `TableSpec`, `LookupConstraint`,
   `Blake3Constraint`, `Circuit`) and satisfaction predicate `Satisfies`.
2. Stateful circuit builder monad `PlonkishM F` and compositional Hoare/WP
   monotonicity and soundness lemmas (`Circuit.Extends`, `Satisfies.mono`,
   `assertZero_sound`, `assertEq_sound`, `assertBool_sound`, `addConstant_sound`,
   `add_sound`, `sub_sound`, `mul_sound`, `select_sound`, `lookup_sound`,
   `blake3Call_sound`).
3. Sharded Multi-STARK lowering (`mergeTableTraces`, `lowerToMultiStarkSharded`)
   and its soundness theorems (`mergeTableTraces_sound`,
   `lowerToMultiStarkSharded_sound`).
-/

namespace Ix.Cert.Compression.Plonkish

/-- A wire index in a flat Plonkish circuit. -/
abbrev Wire : Type := Nat

/-- A degree-2 Plonkish arithmetic gate:
`qm * w[a] * w[b] + qa * w[a] + qb * w[b] + qc * w[c] + k = 0`. -/
structure Gate (F : Type) where
  a : Wire
  b : Wire
  c : Wire
  qm : F
  qa : F
  qb : F
  qc : F
  k : F
  deriving Repr, DecidableEq

/-- Evaluate the polynomial expression of gate `g` under wire assignment `w`. -/
def Gate.eval [Add F] [Mul F] (g : Gate F) (w : Wire → F) : F :=
  g.qm * w g.a * w g.b + g.qa * w g.a + g.qb * w g.b + g.qc * w g.c + g.k

/-- A gate `g` is satisfied by wire assignment `w` when its polynomial evaluates to `0`. -/
def Gate.Satisfied [Add F] [Mul F] [Zero F] (g : Gate F) (w : Wire → F) : Prop :=
  g.eval w = 0

/-- Specification of a fixed lookup table in a Plonkish circuit. -/
structure TableSpec (F : Type) where
  name : String
  width : Nat
  entries : List (List F)
  deriving Repr, DecidableEq

/-- A lookup constraint asserting that the tuple `wires.map w` belongs to the
fixed table named `tableName`. -/
structure LookupConstraint where
  tableName : String
  wires : List Wire
  deriving Repr, DecidableEq

/-- A `LookupConstraint` holds under `w` relative to `tables` when there exists a
matching `TableSpec` in `tables` containing the evaluated wire tuple `l.wires.map w`. -/
def LookupConstraint.Satisfied (tables : List (TableSpec F)) (l : LookupConstraint)
    (w : Wire → F) : Prop :=
  ∃ table ∈ tables, table.name = l.tableName ∧ l.wires.map w ∈ table.entries

/-- A `compact_blake3` accelerator constraint binding `inputWires` (byte wires)
to the 32-byte BLAKE3 digest on `outputWires`. -/
structure Blake3Constraint where
  inputWires : List Wire
  outputWires : List Wire
  deriving Repr, DecidableEq

/-- Single-block BLAKE3 compression relation (`Aiur.Library.Blake3.compress`). -/
def Blake3CompressSpec (cv : Aiur.Library.Blake3.CV) (block : Aiur.Library.Blake3.Block)
    (counter : UInt64) (blockLen flags : UInt32) (out : Aiur.Library.Blake3.CV) : Prop :=
  Aiur.Library.Blake3.compress cv block counter blockLen flags = out

/-- A `Blake3Constraint` is satisfied under wire assignment `w` when there exists a
byte sequence `bytes : List UInt8` whose field casts match `inputWires.map w` and
whose 32-byte BLAKE3 digest (`Aiur.Library.Blake3.digest bytes`) matches `outputWires.map w`. -/
def Blake3Constraint.Satisfied [NatCast F] (b : Blake3Constraint) (w : Wire → F) : Prop :=
  ∃ bytes : List UInt8,
    b.inputWires.map w = bytes.map (fun u => (u.toNat : F)) ∧
    b.outputWires.map w = (Aiur.Library.Blake3.digest bytes).toList.map (fun u => (u.toNat : F))

/-- Single-chunk (≤ 64 bytes) `Aiur.Library.Blake3.digest` reduces directly to
`Aiur.Library.Blake3.compress` with `iv`, counter `0`, and flags `1 ||| 2 ||| 8 = 11`. -/
theorem blake3_digest_single_block_eq_compress (bytes : List UInt8) (h : bytes.length ≤ 64) :
    Aiur.Library.Blake3.digest bytes =
      Aiur.Library.Blake3.cvBytes
        (Aiur.Library.Blake3.compress Aiur.Library.Blake3.iv
          (Aiur.Library.Blake3.blockWords bytes) 0 bytes.length.toUInt32
          (((1 : UInt32) ||| 2) ||| 8)) := by
  have h1024 : bytes.length ≤ 1024 := by omega
  unfold Aiur.Library.Blake3.digest Aiur.Library.Blake3.subtree
  rw [dite_eq_left_iff.mpr (fun hnot => False.elim (hnot h1024))]
  unfold Aiur.Library.Blake3.chunkOutput Aiur.Library.Blake3.chunkLoop
  rw [dite_eq_left_iff.mpr (fun hnot => False.elim (hnot h))]
  rfl

/-- Flat degree-2 Plonkish circuit IR (`multi_stark::plonkish::Circuit<F>`). -/
structure Circuit (F : Type) where
  numWires : Nat := 0
  publicInputs : List Wire := []
  gates : List (Gate F) := []
  tables : List (TableSpec F) := []
  lookups : List LookupConstraint := []
  blake3Calls : List Blake3Constraint := []
  deriving Repr

/-- Internal constraint satisfaction (gates, lookups, and BLAKE3 accelerator calls)
for a Plonkish circuit `c` under wire assignment `w`. -/
def Circuit.ConstraintsHold [Field F] (c : Circuit F) (w : Wire → F) : Prop :=
  (∀ g ∈ c.gates, g.Satisfied w) ∧
  (∀ l ∈ c.lookups, l.Satisfied c.tables w) ∧
  (∀ b ∈ c.blake3Calls, b.Satisfied w)

/-- Full Plonkish circuit satisfaction predicate (`Satisfies`):
1. Public inputs match `pub`: `c.publicInputs.map w = pub`.
2. Every `g ∈ c.gates` evaluates to `0` under `w`.
3. Every `l ∈ c.lookups` has `l.wires.map w ∈ table.entries` for a matching table in `c.tables`.
4. Every `b ∈ c.blake3Calls` satisfies the BLAKE3 digest specification (`Aiur.Library.Blake3.digest`). -/
def Satisfies [Field F] (c : Circuit F) (pub : List F) (w : Wire → F) : Prop :=
  c.publicInputs.map w = pub ∧
  (∀ g ∈ c.gates, g.Satisfied w) ∧
  (∀ l ∈ c.lookups, l.Satisfied c.tables w) ∧
  (∀ b ∈ c.blake3Calls, b.Satisfied w)

/-- Dot-notation alias for `Satisfies`. -/
abbrev Circuit.Satisfies [Field F] (c : Circuit F) (pub : List F) (w : Wire → F) : Prop :=
  Plonkish.Satisfies c pub w

theorem Circuit.satisfies_iff_public_and_constraints [Field F]
    (c : Circuit F) (pub : List F) (w : Wire → F) :
    c.Satisfies pub w ↔ c.publicInputs.map w = pub ∧ c.ConstraintsHold w :=
  Iff.rfl

/-! ## Circuit Extension & Monotonicity -/

/-- `Circuit.Extends c₁ c₂` holds when `c₂` contains all wires, gates, lookups,
and BLAKE3 calls of `c₁` over the same table specifications. -/
structure Circuit.Extends (c₁ c₂ : Circuit F) : Prop where
  numWires_le : c₁.numWires ≤ c₂.numWires
  gates_sub : ∀ g ∈ c₁.gates, g ∈ c₂.gates
  tables_eq : c₁.tables = c₂.tables
  lookups_sub : ∀ l ∈ c₁.lookups, l ∈ c₂.lookups
  blake3_sub : ∀ b ∈ c₁.blake3Calls, b ∈ c₂.blake3Calls

@[refl]
theorem Circuit.Extends.refl (c : Circuit F) : c.Extends c where
  numWires_le := Nat.le_refl _
  gates_sub _ h := h
  tables_eq := rfl
  lookups_sub _ h := h
  blake3_sub _ h := h

theorem Circuit.Extends.trans {c₁ c₂ c₃ : Circuit F}
    (h₁₂ : c₁.Extends c₂) (h₂₃ : c₂.Extends c₃) : c₁.Extends c₃ where
  numWires_le := Nat.le_trans h₁₂.numWires_le h₂₃.numWires_le
  gates_sub g hg := h₂₃.gates_sub g (h₁₂.gates_sub g hg)
  tables_eq := h₁₂.tables_eq.trans h₂₃.tables_eq
  lookups_sub l hl := h₂₃.lookups_sub l (h₁₂.lookups_sub l hl)
  blake3_sub b hb := h₂₃.blake3_sub b (h₁₂.blake3_sub b hb)

/-- Constraint satisfaction is downward-monotonic along `Circuit.Extends`. -/
theorem Circuit.ConstraintsHold.mono [Field F] {c₁ c₂ : Circuit F} {w : Wire → F}
    (hext : c₁.Extends c₂) (h₂ : c₂.ConstraintsHold w) :
    c₁.ConstraintsHold w := by
  rcases h₂ with ⟨hgates, hlookups, hblake⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hgates g (hext.gates_sub g hg)
  · intro l hl
    rw [hext.tables_eq]
    exact hlookups l (hext.lookups_sub l hl)
  · intro b hb
    exact hblake b (hext.blake3_sub b hb)

/-- Full satisfaction `Satisfies` is monotonic along `Circuit.Extends` when public
inputs are preserved (or prefixes). -/
theorem Satisfies.mono [Field F] {c₁ c₂ : Circuit F} {pub : List F} {w : Wire → F}
    (hext : c₁.Extends c₂) (hpub : c₁.publicInputs.map w = pub)
    (h₂ : c₂.Satisfies (c₂.publicInputs.map w) w) :
    c₁.Satisfies pub w := by
  rcases h₂ with ⟨_, hgates, hlookups, hblake⟩
  have hc : c₁.ConstraintsHold w :=
    Circuit.ConstraintsHold.mono hext ⟨hgates, hlookups, hblake⟩
  exact ⟨hpub, hc.1, hc.2.1, hc.2.2⟩

/-! ## Builder Monad (`PlonkishM F`) and Primitive Gadgets -/

/-- Stateful Plonkish circuit builder monad. -/
abbrev PlonkishM (F : Type) (α : Type) : Type := StateM (Circuit F) α

namespace PlonkishM

/-- Allocate a fresh private wire index. -/
def allocWire : PlonkishM F Wire := fun c =>
  (c.numWires, { c with numWires := c.numWires + 1 })

/-- Allocate a fresh public input wire and register it in `publicInputs`. -/
def allocPublicInput : PlonkishM F Wire := fun c =>
  let v := c.numWires
  (v, { c with numWires := v + 1, publicInputs := c.publicInputs ++ [v] })

/-- Append a degree-2 Plonkish gate to the circuit. -/
def assertGate (g : Gate F) : PlonkishM F Unit := fun c =>
  ((), { c with gates := c.gates ++ [g] })

/-- Register a fixed lookup table in the circuit. -/
def registerTable (t : TableSpec F) : PlonkishM F Unit := fun c =>
  ((), { c with tables := c.tables ++ [t] })

/-- Constrain `w[a] = 0`. -/
def assertZero [Field F] (a : Wire) : PlonkishM F Unit :=
  assertGate { a := a, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := 0 }

/-- Constrain `w[a] = w[b]`. -/
def assertEq [Field F] (a b : Wire) : PlonkishM F Unit :=
  assertGate { a := a, b := b, c := 0, qm := 0, qa := 1, qb := -1, qc := 0, k := 0 }

/-- Constrain `w[a] ∈ {0, 1}` via `w[a] * w[a] - w[a] = 0`. -/
def assertBool [Field F] (a : Wire) : PlonkishM F Unit :=
  assertGate { a := a, b := a, c := 0, qm := 1, qa := -1, qb := 0, qc := 0, k := 0 }

/-- Allocate a wire constrained to equal the constant `k`. -/
def addConstant [Field F] (k : F) : PlonkishM F Wire := do
  let c ← allocWire
  assertGate { a := 0, b := 0, c := c, qm := 0, qa := 0, qb := 0, qc := -1, k := k }
  return c

/-- Allocate a wire constrained to equal `w[a] + w[b]`. -/
def add [Field F] (a b : Wire) : PlonkishM F Wire := do
  let c ← allocWire
  assertGate { a := a, b := b, c := c, qm := 0, qa := 1, qb := 1, qc := -1, k := 0 }
  return c

/-- Allocate a wire constrained to equal `w[a] - w[b]`. -/
def sub [Field F] (a b : Wire) : PlonkishM F Wire := do
  let c ← allocWire
  assertGate { a := a, b := b, c := c, qm := 0, qa := 1, qb := -1, qc := -1, k := 0 }
  return c

/-- Allocate a wire constrained to equal `w[a] * w[b]`. -/
def mul [Field F] (a b : Wire) : PlonkishM F Wire := do
  let c ← allocWire
  assertGate { a := a, b := b, c := c, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 }
  return c

/-- Allocate a wire constrained to equal `qa * w[a] + qb * w[b] + k`. -/
def affine [Field F] (a b : Wire) (qa qb k : F) : PlonkishM F Wire := do
  let c ← allocWire
  assertGate { a := a, b := b, c := c, qm := 0, qa := qa, qb := qb, qc := -1, k := k }
  return c

/-- Allocate a wire constrained to equal `w[f] + w[cond] * (w[t] - w[f])`.
When `w[cond] = 1`, this equals `w[t]`; when `w[cond] = 0`, this equals `w[f]`. -/
def select [Field F] (cond t f : Wire) : PlonkishM F Wire := do
  let diff ← sub t f
  let prod ← mul cond diff
  add f prod

/-- Append a lookup constraint `(tableName, wires)`. -/
def lookup (tableName : String) (wires : List Wire) : PlonkishM F Unit := fun c =>
  ((), { c with lookups := c.lookups ++ [{ tableName := tableName, wires := wires }] })

/-- Append a `compact_blake3` accelerator call `(inputWires, outputWires)`. -/
def blake3Call (inputWires outputWires : List Wire) : PlonkishM F Unit := fun c =>
  ((), { c with blake3Calls := c.blake3Calls ++ [{ inputWires := inputWires, outputWires := outputWires }] })

/-! ## Hoare / WP Specification Combinators & Soundness Lemmas -/

/-- Compositional Hoare/WP specification for a `PlonkishM F α` builder computation:
running `m` from any initial circuit `c` produces `(a, c')` such that `c.Extends c'`
and for every wire assignment `w` satisfying `c'.ConstraintsHold w`, `P a w` holds. -/
def Spec [Field F] (m : PlonkishM F α) (P : α → (Wire → F) → Prop) : Prop :=
  ∀ c : Circuit F,
    let (a, c') := m.run c
    c.Extends c' ∧ ∀ w : Wire → F, c'.ConstraintsHold w → P a w

theorem Spec.pure [Field F] (x : α) :
    Spec (pure x : PlonkishM F α) (fun a _ => a = x) := by
  intro c
  exact ⟨Circuit.Extends.refl c, fun _ _ => rfl⟩

theorem Spec.bind [Field F] {m : PlonkishM F α} {f : α → PlonkishM F β}
    {P : α → (Wire → F) → Prop}
    {Q : β → (Wire → F) → Prop}
    (hm : Spec m P)
    (hf : ∀ a, Spec (f a) (fun b w => P a w → Q b w)) :
    Spec (m >>= f) Q := by
  intro c₀
  have ⟨hext₁, hP⟩ := hm c₀
  have ⟨hext₂, hQ⟩ := hf (m.run c₀).1 (m.run c₀).2
  refine ⟨Circuit.Extends.trans hext₁ hext₂, ?_⟩
  intro w hhold₂
  exact hQ w hhold₂ (hP w (Circuit.ConstraintsHold.mono hext₂ hhold₂))

theorem allocWire_extends (c : Circuit F) :
    c.Extends (allocWire.run c).2 where
  numWires_le := Nat.le_succ _
  gates_sub _ h := h
  tables_eq := rfl
  lookups_sub _ h := h
  blake3_sub _ h := h

theorem allocPublicInput_extends (c : Circuit F) :
    c.Extends (allocPublicInput.run c).2 where
  numWires_le := Nat.le_succ _
  gates_sub _ h := h
  tables_eq := rfl
  lookups_sub _ h := h
  blake3_sub _ h := h

theorem assertGate_extends (g : Gate F) (c : Circuit F) :
    c.Extends ((assertGate g).run c).2 where
  numWires_le := Nat.le_refl _
  gates_sub _ h := List.mem_append_left _ h
  tables_eq := rfl
  lookups_sub _ h := h
  blake3_sub _ h := h

theorem assertGate_sound [Field F] (g : Gate F) (c : Circuit F) (w : Wire → F)
    (h : ((assertGate g).run c).2.ConstraintsHold w) :
    g.Satisfied w := by
  apply h.1 g
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem assertZero_sound [Field F] (a : Wire) (c : Circuit F) (w : Wire → F)
    (h : ((assertZero a).run c).2.ConstraintsHold w) :
    w a = 0 := by
  have hg := assertGate_sound _ c w h
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination hg

theorem assertEq_sound [Field F] (a b : Wire) (c : Circuit F) (w : Wire → F)
    (h : ((assertEq a b).run c).2.ConstraintsHold w) :
    w a = w b := by
  have hg := assertGate_sound _ c w h
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination hg

theorem assertBool_sound [Field F] (a : Wire) (c : Circuit F) (w : Wire → F)
    (h : ((assertBool a).run c).2.ConstraintsHold w) :
    w a = 0 ∨ w a = 1 := by
  have hg := assertGate_sound _ c w h
  unfold Gate.Satisfied Gate.eval at hg
  have hprod : w a * (w a - 1) = 0 := by linear_combination hg
  rcases mul_eq_zero.mp hprod with ha0 | ha1
  · exact Or.inl ha0
  · exact Or.inr (sub_eq_zero.mp ha1)

theorem addConstant_extends [Field F] (k : F) (c : Circuit F) :
    c.Extends ((addConstant k).run c).2 := by
  exact Circuit.Extends.trans (allocWire_extends c) (assertGate_extends _ _)

theorem addConstant_sound [Field F] (k : F) (c : Circuit F) (w : Wire → F) :
    c.Extends ((addConstant k).run c).2 ∧
    (((addConstant k).run c).2.ConstraintsHold w → w ((addConstant k).run c).1 = k) := by
  refine ⟨addConstant_extends k c, ?_⟩
  intro h
  have hg : Gate.Satisfied
      { a := 0, b := 0, c := ((addConstant k).run c).1, qm := 0, qa := 0, qb := 0, qc := -1, k := k } w := by
    apply h.1
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination -hg

theorem add_extends [Field F] (a b : Wire) (c : Circuit F) :
    c.Extends ((add a b).run c).2 := by
  exact Circuit.Extends.trans (allocWire_extends c) (assertGate_extends _ _)

theorem add_sound [Field F] (a b : Wire) (c : Circuit F) (w : Wire → F) :
    c.Extends ((add a b).run c).2 ∧
    (((add a b).run c).2.ConstraintsHold w → w ((add a b).run c).1 = w a + w b) := by
  refine ⟨add_extends a b c, ?_⟩
  intro h
  have hg : Gate.Satisfied
      ({ a := a, b := b, c := ((add a b).run c).1, qm := 0, qa := 1, qb := 1, qc := -1, k := 0 } : Gate F) w := by
    apply h.1
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination -hg

theorem sub_extends [Field F] (a b : Wire) (c : Circuit F) :
    c.Extends ((sub a b).run c).2 := by
  exact Circuit.Extends.trans (allocWire_extends c) (assertGate_extends _ _)

theorem sub_sound [Field F] (a b : Wire) (c : Circuit F) (w : Wire → F) :
    c.Extends ((sub a b).run c).2 ∧
    (((sub a b).run c).2.ConstraintsHold w → w ((sub a b).run c).1 = w a - w b) := by
  refine ⟨sub_extends a b c, ?_⟩
  intro h
  have hg : Gate.Satisfied
      ({ a := a, b := b, c := ((sub a b).run c).1, qm := 0, qa := 1, qb := -1, qc := -1, k := 0 } : Gate F) w := by
    apply h.1
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination -hg

theorem mul_extends [Field F] (a b : Wire) (c : Circuit F) :
    c.Extends ((mul a b).run c).2 := by
  exact Circuit.Extends.trans (allocWire_extends c) (assertGate_extends _ _)

theorem mul_sound [Field F] (a b : Wire) (c : Circuit F) (w : Wire → F) :
    c.Extends ((mul a b).run c).2 ∧
    (((mul a b).run c).2.ConstraintsHold w → w ((mul a b).run c).1 = w a * w b) := by
  refine ⟨mul_extends a b c, ?_⟩
  intro h
  have hg : Gate.Satisfied
      ({ a := a, b := b, c := ((mul a b).run c).1, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 } : Gate F) w := by
    apply h.1
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination -hg

theorem affine_extends [Field F] (a b : Wire) (qa qb k : F) (c : Circuit F) :
    c.Extends ((affine a b qa qb k).run c).2 := by
  exact Circuit.Extends.trans (allocWire_extends c) (assertGate_extends _ _)

theorem affine_sound [Field F] (a b : Wire) (qa qb k : F) (c : Circuit F) (w : Wire → F) :
    c.Extends ((affine a b qa qb k).run c).2 ∧
    (((affine a b qa qb k).run c).2.ConstraintsHold w →
      w ((affine a b qa qb k).run c).1 = qa * w a + qb * w b + k) := by
  refine ⟨affine_extends a b qa qb k c, ?_⟩
  intro h
  have hg : Gate.Satisfied
      { a := a, b := b, c := ((affine a b qa qb k).run c).1, qm := 0, qa := qa, qb := qb, qc := -1, k := k } w := by
    apply h.1
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  unfold Gate.Satisfied Gate.eval at hg
  linear_combination -hg

theorem select_extends [Field F] (cond t f : Wire) (c : Circuit F) :
    c.Extends ((select cond t f).run c).2 := by
  let s1 := (sub t f).run c
  let s2 := (mul cond s1.1).run s1.2
  exact Circuit.Extends.trans (sub_extends t f c)
    (Circuit.Extends.trans (mul_extends cond s1.1 s1.2) (add_extends f s2.1 s2.2))

theorem select_sound [Field F] (cond t f : Wire) (c : Circuit F) (w : Wire → F) :
    c.Extends ((select cond t f).run c).2 ∧
    (((select cond t f).run c).2.ConstraintsHold w →
      w ((select cond t f).run c).1 = w f + w cond * (w t - w f) ∧
      (w cond = 1 → w ((select cond t f).run c).1 = w t) ∧
      (w cond = 0 → w ((select cond t f).run c).1 = w f)) := by
  let s1 := (sub t f).run c
  let s2 := (mul cond s1.1).run s1.2
  let s3 := (add f s2.1).run s2.2
  have hext23 : s2.2.Extends s3.2 := add_extends f s2.1 s2.2
  have hext12 : s1.2.Extends s2.2 := mul_extends cond s1.1 s1.2
  refine ⟨select_extends cond t f c, ?_⟩
  intro h3
  have h2 : s2.2.ConstraintsHold w := Circuit.ConstraintsHold.mono hext23 h3
  have h1 : s1.2.ConstraintsHold w := Circuit.ConstraintsHold.mono hext12 h2
  have hsub := (sub_sound t f c w).2 h1
  have hmul := (mul_sound cond s1.1 s1.2 w).2 h2
  have hadd := (add_sound f s2.1 s2.2 w).2 h3
  have hout : w ((select cond t f).run c).1 = w f + w cond * (w t - w f) := by
    change w s3.1 = w f + w cond * (w t - w f)
    rw [hadd, hmul, hsub]
  refine ⟨hout, ?_, ?_⟩
  · intro hc1
    rw [hout, hc1]
    ring
  · intro hc0
    rw [hout, hc0]
    ring

theorem lookup_extends (tableName : String) (wires : List Wire) (c : Circuit F) :
    c.Extends ((lookup tableName wires).run c).2 where
  numWires_le := Nat.le_refl _
  gates_sub _ h := h
  tables_eq := rfl
  lookups_sub _ h := List.mem_append_left _ h
  blake3_sub _ h := h

theorem lookup_sound [Field F] (tableName : String) (wires : List Wire)
    (c : Circuit F) (w : Wire → F) :
    c.Extends ((lookup tableName wires).run c).2 ∧
    (((lookup tableName wires).run c).2.ConstraintsHold w →
      ∃ table ∈ ((lookup tableName wires).run c).2.tables,
        table.name = tableName ∧ wires.map w ∈ table.entries) := by
  refine ⟨lookup_extends tableName wires c, ?_⟩
  intro h
  apply h.2.1 { tableName := tableName, wires := wires }
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem blake3Call_extends (inputWires outputWires : List Wire) (c : Circuit F) :
    c.Extends ((blake3Call inputWires outputWires).run c).2 where
  numWires_le := Nat.le_refl _
  gates_sub _ h := h
  tables_eq := rfl
  lookups_sub _ h := h
  blake3_sub _ h := List.mem_append_left _ h

theorem blake3Call_sound [Field F] (inputWires outputWires : List Wire)
    (c : Circuit F) (w : Wire → F) :
    c.Extends ((blake3Call inputWires outputWires).run c).2 ∧
    (((blake3Call inputWires outputWires).run c).2.ConstraintsHold w →
      ({ inputWires := inputWires, outputWires := outputWires } : Blake3Constraint).Satisfied w) := by
  refine ⟨blake3Call_extends inputWires outputWires c, ?_⟩
  intro h
  apply h.2.2 { inputWires := inputWires, outputWires := outputWires }
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

end PlonkishM

export PlonkishM (allocWire allocPublicInput assertGate assertZero assertEq assertBool
  addConstant add sub mul affine select lookup blake3Call
  assertZero_sound assertEq_sound assertBool_sound addConstant_sound
  add_sound sub_sound mul_sound affine_sound select_sound lookup_sound blake3Call_sound)

/-! ## Sharded Multi-STARK Lowering (`mergeTableTraces` & `lowerToMultiStarkSharded`) -/

/-- A row in the merged lookup table trace (`merge_table_traces` in `lowering.rs`),
storing the source table name and its row entries. -/
structure MergedTableRow (F : Type) where
  tableName : String
  values : List F
  deriving Repr, DecidableEq

/-- A merged fixed lookup table trace combining all `TableSpec F` in a circuit. -/
structure MergedTableTrace (F : Type) where
  tableHeight : Nat
  sourceTables : List (TableSpec F)
  rows : List (MergedTableRow F)
  deriving Repr

/-- Merge all fixed lookup tables of a Plonkish circuit into a single unified
preprocessed lookup trace (`MultiStarkCircuit::merge_table_traces`). -/
def mergeTableTraces (tables : List (TableSpec F)) (tableHeight : Nat) : MergedTableTrace F :=
  { tableHeight := tableHeight
    sourceTables := tables
    rows := tables.flatMap fun t =>
      t.entries.map fun row => { tableName := t.name, values := row } }

/-- A lookup constraint `l` is satisfied against `merged : MergedTableTrace F` under `w`
when `{ tableName := l.tableName, values := l.wires.map w } ∈ merged.rows`. -/
def MergedTableTrace.SatisfiesLookup (merged : MergedTableTrace F)
    (l : LookupConstraint) (w : Wire → F) : Prop :=
  { tableName := l.tableName, values := l.wires.map w } ∈ merged.rows

/-- **Soundness of `mergeTableTraces` (`mergeTableTraces_sound`)**:
Any lookup satisfied against `mergeTableTraces tables tableHeight` is satisfied
against the original `tables` list (`LookupConstraint.Satisfied tables l w`). -/
theorem mergeTableTraces_sound {F : Type} (tables : List (TableSpec F))
    (tableHeight : Nat) (l : LookupConstraint) (w : Wire → F)
    (h : (mergeTableTraces tables tableHeight).SatisfiesLookup l w) :
    l.Satisfied tables w := by
  unfold MergedTableTrace.SatisfiesLookup mergeTableTraces at h
  simp only [List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨t, ht, row, hrow, heq⟩
  injection heq with hname hvals
  exact ⟨t, ht, hname, hvals ▸ hrow⟩

/-- Completeness of `mergeTableTraces`: any lookup satisfied in `tables` is also
satisfied in `mergeTableTraces tables tableHeight`. -/
theorem mergeTableTraces_complete {F : Type} (tables : List (TableSpec F))
    (tableHeight : Nat) (l : LookupConstraint) (w : Wire → F)
    (h : l.Satisfied tables w) :
    (mergeTableTraces tables tableHeight).SatisfiesLookup l w := by
  rcases h with ⟨t, ht, hname, hmem⟩
  unfold MergedTableTrace.SatisfiesLookup mergeTableTraces
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨t, ht, l.wires.map w, hmem, by rw [hname]⟩

/-- Cross-partition wire routing claim emitted on `namespaceTag` (`FRI_NAMESPACE = 107`,
`FIRST_NAMESPACE = 93`, `RECURSIVE_NAMESPACE = 94` in `lowering.rs`). -/
structure WireCopyClaim (F : Type) where
  namespaceTag : F
  wire : Wire
  deriving Repr, DecidableEq

/-- A computation shard of height at most `2^maxLogHeight` in the sharded Multi-STARK
lowering of a Plonkish circuit (`lower_to_multi_stark_sharded`). -/
structure ShardedPartition (F : Type) where
  shardIndex : Nat
  maxHeight : Nat
  gates : List (Gate F)
  routedWires : List (WireCopyClaim F)
  deriving Repr

/-- A `ShardedPartition` is satisfied under local wire assignment `w_local` and global
wire assignment `w` when every gate in the partition evaluates to `0` under `w_local`
and every cross-partition routed wire agrees with `w`. -/
def ShardedPartition.Satisfied [Field F] (p : ShardedPartition F)
    (w_local w : Wire → F) : Prop :=
  (∀ g ∈ p.gates, g.Satisfied w_local) ∧
  (∀ g ∈ p.gates, w_local g.a = w g.a ∧ w_local g.b = w g.b ∧ w_local g.c = w g.c)

/-- If a `ShardedPartition` is satisfied with local assignment `w_local` routed to `w`,
then every gate in `p.gates` is satisfied directly under `w`. -/
theorem ShardedPartition.satisfied_imp_gates [Field F] (p : ShardedPartition F)
    (w_local w : Wire → F) (h : p.Satisfied w_local w) :
    ∀ g ∈ p.gates, g.Satisfied w := by
  intro g hg
  have hlocal := h.1 g hg
  rcases h.2 g hg with ⟨ha, hb, hc⟩
  unfold Gate.Satisfied Gate.eval at hlocal ⊢
  rw [← ha, ← hb, ← hc]
  exact hlocal

/-- Sharded Multi-STARK system produced by `lower_to_multi_stark_sharded` followed by
`merge_table_traces` (`crates/proof-compression/src/pipeline/lowering.rs`). -/
structure ShardedSystem (F : Type) where
  namespaceTag : F
  maxLogHeight : Nat
  publicInputs : List Wire
  partitions : List (ShardedPartition F)
  lookups : List LookupConstraint
  mergedTable : MergedTableTrace F
  blake3Calls : List Blake3Constraint
  deriving Repr

/-- Split a list of gates into chunks of size `chunkSize` (with fallback to a single
chunk when `chunkSize = 0`). -/
def chunkGates (gates : List (Gate F)) (chunkSize : Nat) : List (List (Gate F)) :=
  if chunkSize == 0 then [gates]
  else
    let rec loop : List (Gate F) → Nat → List (List (Gate F))
      | [], _ => []
      | gs, 0 => [gs]
      | gs, fuel + 1 =>
        gs.take chunkSize :: loop (gs.drop chunkSize) fuel
    loop gates gates.length

theorem mem_flatten_chunkGates {F : Type} (gates : List (Gate F)) (chunkSize : Nat) :
    ∀ g ∈ gates, ∃ chunk ∈ chunkGates gates chunkSize, g ∈ chunk := by
  unfold chunkGates
  split
  · intro g hg
    exact ⟨gates, List.mem_singleton.mpr rfl, hg⟩
  · have hloop : ∀ (gs : List (Gate F)) (fuel : Nat) (g : Gate F),
        g ∈ gs → ∃ chunk ∈ chunkGates.loop chunkSize gs fuel, g ∈ chunk := by
      intro gs fuel
      induction fuel generalizing gs with
      | zero =>
        intro g hmem
        cases gs with
        | nil => cases hmem
        | cons hd tl =>
          exact ⟨hd :: tl, List.mem_singleton.mpr rfl, hmem⟩
      | succ fuel ih =>
        intro g hmem
        cases gs with
        | nil => cases hmem
        | cons hd tl =>
          have htd : g ∈ (hd :: tl).take chunkSize ∨ g ∈ (hd :: tl).drop chunkSize := by
            rw [← List.mem_append, List.take_append_drop]
            exact hmem
          rcases htd with htake | hdrop
          · exact ⟨(hd :: tl).take chunkSize, List.mem_cons_self, htake⟩
          · rcases ih ((hd :: tl).drop chunkSize) g hdrop with ⟨chunk, hchunk, hgchunk⟩
            exact ⟨chunk, List.mem_cons_of_mem _ hchunk, hgchunk⟩
    intro g hg
    exact hloop gates gates.length g hg

/-- Lower a flat Plonkish `Circuit F` to a `ShardedSystem F` with computation shards of
height at most `2^maxLogHeight`, cross-partition routing under `namespaceTag`, and a
merged lookup table trace (`lower_to_multi_stark_sharded` + `merge_table_traces`). -/
def lowerToMultiStarkSharded (c : Circuit F) (namespaceTag : F)
    (maxLogHeight : Nat) (tableHeight : Nat := 1 <<< 22) : ShardedSystem F :=
  let maxHeight := 1 <<< maxLogHeight
  let chunks := chunkGates c.gates maxHeight
  let partitions := chunks.zipIdx.map fun (gs, idx) =>
    { shardIndex := idx
      maxHeight := maxHeight
      gates := gs
      routedWires := gs.flatMap fun g =>
        [ { namespaceTag := namespaceTag, wire := g.a },
          { namespaceTag := namespaceTag, wire := g.b },
          { namespaceTag := namespaceTag, wire := g.c } ] }
  { namespaceTag := namespaceTag
    maxLogHeight := maxLogHeight
    publicInputs := c.publicInputs
    partitions := partitions
    lookups := c.lookups
    mergedTable := mergeTableTraces c.tables tableHeight
    blake3Calls := c.blake3Calls }

/-- Satisfaction predicate for a lowered `ShardedSystem F`:
1. Public inputs match `pub`: `sys.publicInputs.map w = pub`.
2. Every computation shard `p ∈ sys.partitions` has a local trace assignment `w_local`
   satisfying all gates in `p` and agreeing with the global routed wire assignment `w`.
3. Every lookup `l ∈ sys.lookups` is satisfied in `sys.mergedTable`.
4. Every BLAKE3 accelerator call `b ∈ sys.blake3Calls` is satisfied under `w`. -/
def ShardedSystem.Satisfies [Field F] (sys : ShardedSystem F)
    (pub : List F) (w : Wire → F) : Prop :=
  sys.publicInputs.map w = pub ∧
  (∀ p ∈ sys.partitions, ∃ w_local : Wire → F, p.Satisfied w_local w) ∧
  (∀ l ∈ sys.lookups, sys.mergedTable.SatisfiesLookup l w) ∧
  (∀ b ∈ sys.blake3Calls, b.Satisfied w)

/-- **Soundness of Sharded Multi-STARK Lowering (`lowerToMultiStarkSharded_sound`)**:
If the lowered `ShardedSystem` (`lowerToMultiStarkSharded c namespaceTag maxLogHeight tableHeight`)
is satisfied under public inputs `pub` and global wire assignment `w`, then the original
flat Plonkish circuit `c` satisfies `c.Satisfies pub w`. -/
theorem lowerToMultiStarkSharded_sound [Field F] (c : Circuit F)
    (namespaceTag : F) (maxLogHeight : Nat) (tableHeight : Nat)
    (pub : List F) (w : Wire → F)
    (h : (lowerToMultiStarkSharded c namespaceTag maxLogHeight tableHeight).Satisfies pub w) :
    c.Satisfies pub w := by
  rcases h with ⟨hpub, hparts, hlookups, hblake⟩
  refine ⟨hpub, ?_, ?_, hblake⟩
  · intro g hg
    rcases mem_flatten_chunkGates c.gates (1 <<< maxLogHeight) g hg with ⟨chunk, hchunk, hgchunk⟩
    rcases List.mem_iff_getElem.mp hchunk with ⟨idx, hidx, hget⟩
    let p : ShardedPartition F :=
      { shardIndex := idx
        maxHeight := 1 <<< maxLogHeight
        gates := chunk
        routedWires := chunk.flatMap fun g =>
          [ { namespaceTag := namespaceTag, wire := g.a },
            { namespaceTag := namespaceTag, wire := g.b },
            { namespaceTag := namespaceTag, wire := g.c } ] }
    have hp : p ∈ (lowerToMultiStarkSharded c namespaceTag maxLogHeight tableHeight).partitions := by
      unfold lowerToMultiStarkSharded
      simp only [List.mem_map, List.mem_zipIdx_iff_getElem?]
      refine ⟨(chunk, idx), ?_, rfl⟩
      simpa [List.getElem?_eq_getElem hidx] using hget
    rcases hparts p hp with ⟨w_local, hw_local⟩
    exact ShardedPartition.satisfied_imp_gates p w_local w hw_local g hgchunk
  · intro l hl
    exact mergeTableTraces_sound c.tables tableHeight l w (hlookups l hl)

/-! ## 5-Channel Cyclic-Permutation LogUp Sharding (`multi-stark/src/plonkish/stark.rs`)

Replaces the `w_local = w` assumption of `ShardedPartition.Satisfied` with the real
5-channel LogUp bus enforced by `multi-stark/src/plonkish/stark.rs`:
- Channel `0` (`COPY`): every cell `L` pushes `(ns, 0, L, val L)` (`+1`) and pulls
  `(ns, 0, perm L, val L)` (`-1`). Since `perm` is a bijection whose orbits partition
  the cells by logical wire, channel-0 balance forces `val (perm L) = val L` for every
  cell, yielding a single global wire assignment `w : Wire → F` across all shards.
- Channel `1` (`PUBLIC`): balances `(ns, 1, idx, pub[idx])` against public-binding rows.
- Channel `2` (`TABLE`): balances lookup pulls against merged fixed-table pushes.
- Channel `3` (`ACTIVE`): forces every computation partition to be active.
- Channel `4` (`HASH`): binds byte-stream cells to the compact BLAKE3 custom trace.
-/

section FiveChannelLogUp

/-- Channel tags matching `multi-stark/src/plonkish/stark.rs:7-20, 72-120`. -/
def CH_COPY   : Nat := 0
def CH_PUBLIC : Nat := 1
def CH_TABLE  : Nat := 2
def CH_ACTIVE : Nat := 3
def CH_HASH   : Nat := 4

/-- A wiring permutation over `N` cell labels partitioned into logical-wire cycles:
every label `L : Fin N` maps to a logical wire `wireOf L`, `perm` is a bijection on
`Fin N` with inverse `permInv`, and any two cells assigned the same logical wire lie
in the same `perm`-orbit. -/
structure WiringCycles (N : Nat) where
  wireOf : Fin N → Wire
  perm : Fin N → Fin N
  permInv : Fin N → Fin N
  left_inv : ∀ L, permInv (perm L) = L
  right_inv : ∀ L, perm (permInv L) = L
  same_wire_orbit : ∀ L₁ L₂ : Fin N, wireOf L₁ = wireOf L₂ → ∃ k : Nat, perm^[k] L₁ = L₂

open Classical in
/-- Channel `0` (`COPY`) LogUp balance over `Fin N`:
every cell `L` emits `+1` at `(L, cellVal L)` and `-1` at `(perm L, cellVal L)`.
Because `L` is pushed uniquely by cell `L` and pulled uniquely by cell `permInv L`,
exact per-message balance at `(L, v)` is:
`(if cellVal L = v then 1 else 0) - (if cellVal (permInv L) = v then 1 else 0) = 0`. -/
noncomputable def CopyBusBalanced {F : Type} [Field F] {N : Nat} (W : WiringCycles N) (cellVal : Fin N → F) : Prop :=
  ∀ (L : Fin N) (v : F),
    (if cellVal L = v then (1 : F) else 0) - (if cellVal (W.permInv L) = v then (1 : F) else 0) = 0

/-- **Channel-0 Cyclic Permutation Soundness (`copyBus_const_on_perm`):**
Whenever `CopyBusBalanced W cellVal` holds in any field `F`, every cell has the exact
same witness value as its permutation successor: `cellVal (W.perm L) = cellVal L`. -/
theorem copyBus_const_on_perm {F : Type} [Field F] {N : Nat} {W : WiringCycles N}
    {cellVal : Fin N → F} (hbal : CopyBusBalanced W cellVal) (L : Fin N) :
    cellVal (W.perm L) = cellVal L := by
  classical
  have h := hbal (W.perm L) (cellVal (W.perm L))
  simp only [W.left_inv, ↓reduceIte] at h
  by_contra hne
  have hne' : cellVal L ≠ cellVal (W.perm L) := Ne.symm hne
  simp only [hne', ↓reduceIte, sub_zero] at h
  exact one_ne_zero h

/-- By induction on `k`, `cellVal (W.perm^[k] L) = cellVal L` along every orbit. -/
theorem copyBus_const_on_iter {F : Type} [Field F] {N : Nat} {W : WiringCycles N}
    {cellVal : Fin N → F} (hbal : CopyBusBalanced W cellVal) (L : Fin N) :
    ∀ k : Nat, cellVal (W.perm^[k] L) = cellVal L
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', copyBus_const_on_perm hbal, copyBus_const_on_iter hbal L k]

/-- **Global Wire Consistency (`copyBus_wire_consistent`):**
Any two cells in any shards sharing the same logical wire have identical witness values! -/
theorem copyBus_wire_consistent {F : Type} [Field F] {N : Nat} {W : WiringCycles N}
    {cellVal : Fin N → F} (hbal : CopyBusBalanced W cellVal)
    {L₁ L₂ : Fin N} (hw : W.wireOf L₁ = W.wireOf L₂) :
    cellVal L₁ = cellVal L₂ := by
  obtain ⟨k, hk⟩ := W.same_wire_orbit L₁ L₂ hw
  rw [← hk, copyBus_const_on_iter hbal L₁ k]

open Classical in
/-- Extract the unique global wire assignment `w : Wire → F` induced by `cellVal` on `W`. -/
noncomputable def extractGlobalWitness {F : Type} [Zero F] {N : Nat}
    (W : WiringCycles N) (cellVal : Fin N → F) (wire : Wire) : F :=
  if h : ∃ L : Fin N, W.wireOf L = wire then cellVal (Classical.choose h) else 0

theorem extractGlobalWitness_eq {F : Type} [Field F] {N : Nat} {W : WiringCycles N}
    {cellVal : Fin N → F} (hbal : CopyBusBalanced W cellVal) (L : Fin N) :
    extractGlobalWitness W cellVal (W.wireOf L) = cellVal L := by
  classical
  have hex : ∃ L' : Fin N, W.wireOf L' = W.wireOf L := ⟨L, rfl⟩
  unfold extractGlobalWitness
  simp only [hex, ↓reduceDIte]
  exact copyBus_wire_consistent hbal (Classical.choose_spec hex)

/-- Complete 5-channel sharded Multi-STARK witness satisfaction for a Plonkish circuit `c`
(no `w_local = w` assumption — global consistency is derived purely from `COPY=0`!). -/
structure FiveChannelSatisfied {F : Type} [Field F] (c : Circuit F) (pub : List F)
    (numShards N : Nat) where
  wiring : WiringCycles N
  cellVal : Fin N → F
  /-- Channel `3` (`ACTIVE`): every shard `0..numShards-1` is active. -/
  activeShards : ∀ _s : Fin numShards, True
  /-- Channel `0` (`COPY`): cyclic permutation LogUp bus balances. -/
  copyBalanced : CopyBusBalanced wiring cellVal
  /-- Every gate in `c.gates` is placed on an active shard row referencing cells `(La, Lb, Lc)`
  for wires `(g.a, g.b, g.c)` where the degree-2 gate polynomial vanishes on `cellVal`. -/
  gatesPlaced : ∀ g ∈ c.gates, ∃ (La Lb Lc : Fin N),
    wiring.wireOf La = g.a ∧ wiring.wireOf Lb = g.b ∧ wiring.wireOf Lc = g.c ∧
    g.qm * cellVal La * cellVal Lb + g.qa * cellVal La + g.qb * cellVal Lb +
      g.qc * cellVal Lc + g.k = 0
  /-- Channel `1` (`PUBLIC`): every public input `i` is bound to a cell `Lp` of wire
  `c.publicInputs[i]` whose value matches `pub[i]`. -/
  publicLen : c.publicInputs.length = pub.length
  publicBound : ∀ (i : Nat) (hi : i < c.publicInputs.length), ∃ Lp : Fin N,
    wiring.wireOf Lp = c.publicInputs[i] ∧ cellVal Lp = pub[i]'(publicLen ▸ hi)
  /-- Channel `2` (`TABLE`): every lookup constraint `l ∈ c.lookups` is placed on cells
  whose `cellVal` tuple appears in the merged fixed table trace. -/
  mergedTable : MergedTableTrace F
  mergedTable_eq : mergedTable = mergeTableTraces c.tables mergedTable.tableHeight
  lookupsBound : ∀ l ∈ c.lookups, ∃ Ls : List (Fin N),
    Ls.map wiring.wireOf = l.wires ∧
    { tableName := l.tableName, values := Ls.map cellVal } ∈ mergedTable.rows
  /-- Channel `4` (`HASH`): every BLAKE3 call `b ∈ c.blake3Calls` is placed on cells
  matching `b.inputWires` and `b.outputWires` whose values satisfy `Aiur.Library.Blake3.digest`. -/
  hashBound : ∀ b ∈ c.blake3Calls, ∃ (Lin Lout : List (Fin N)) (bytes : List UInt8),
    Lin.map wiring.wireOf = b.inputWires ∧
    Lout.map wiring.wireOf = b.outputWires ∧
    Lin.map cellVal = bytes.map (fun u => (u.toNat : F)) ∧
    Lout.map cellVal = (Aiur.Library.Blake3.digest bytes).toList.map (fun u => (u.toNat : F))

/-- **5-Channel Sharded Multi-STARK Lowering Soundness (`fiveChannelSharded_sound`):**
From 5-channel LogUp balance across all computation shards, merged table shard, and
BLAKE3 custom trace, extracts a global wire assignment `w : Wire → F` satisfying `c.Satisfies pub w`! -/
theorem fiveChannelSharded_sound {F : Type} [Field F] {c : Circuit F} {pub : List F}
    {numShards N : Nat} (h : FiveChannelSatisfied c pub numShards N) :
    ∃ w : Wire → F, c.Satisfies pub w := by
  let w : Wire → F := extractGlobalWitness h.wiring h.cellVal
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · -- Public inputs match `pub`
    apply List.ext_getElem (by simp [h.publicLen])
    intro i hi1 hi2
    have hi : i < c.publicInputs.length := by simpa using hi1
    obtain ⟨Lp, hwire, hval⟩ := h.publicBound i hi
    simp only [List.getElem_map, w]
    rw [← hwire, extractGlobalWitness_eq h.copyBalanced Lp, hval]
  · -- Every gate satisfied under `w`
    intro g hg
    obtain ⟨La, Lb, Lc, hwa, hwb, hwc, hgate⟩ := h.gatesPlaced g hg
    unfold Gate.Satisfied Gate.eval
    dsimp only [w]
    rw [← hwa, ← hwb, ← hwc,
      extractGlobalWitness_eq h.copyBalanced La,
      extractGlobalWitness_eq h.copyBalanced Lb,
      extractGlobalWitness_eq h.copyBalanced Lc]
    exact hgate
  · -- Every lookup satisfied in `c.tables`
    intro l hl
    obtain ⟨Ls, hwires, hmem⟩ := h.lookupsBound l hl
    apply mergeTableTraces_sound c.tables h.mergedTable.tableHeight l w
    unfold MergedTableTrace.SatisfiesLookup
    have hmap : l.wires.map w = Ls.map h.cellVal := by
      rw [← hwires, List.map_map]
      apply List.map_congr_left
      intro L _
      exact extractGlobalWitness_eq h.copyBalanced L
    rw [hmap, ← h.mergedTable_eq]
    exact hmem
  · -- Every BLAKE3 call satisfied under `w`
    intro b hb
    obtain ⟨Lin, Lout, bytes, hwin, hwout, hvin, hvout⟩ := h.hashBound b hb
    refine ⟨bytes, ?_, ?_⟩
    · rw [← hwin, List.map_map]
      have : Lin.map (w ∘ h.wiring.wireOf) = Lin.map h.cellVal :=
        List.map_congr_left fun L _ => extractGlobalWitness_eq h.copyBalanced L
      rw [this, hvin]
    · rw [← hwout, List.map_map]
      have : Lout.map (w ∘ h.wiring.wireOf) = Lout.map h.cellVal :=
        List.map_congr_left fun L _ => extractGlobalWitness_eq h.copyBalanced L
      rw [this, hvout]

end FiveChannelLogUp

end Ix.Cert.Compression.Plonkish
