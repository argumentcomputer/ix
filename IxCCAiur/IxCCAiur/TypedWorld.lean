import IxCCAiur.TypedLower
import IxCCAiur.World

/-! # World Verification for Typed / Demand-Linked Programs (`IxCCAiur.TypedWorld`)

Checks the prepared Formal Aiur source for a typed `LoweredProgram` according
to its linked `TableTier`:
* `.none` — only `World.checkFunctions` (zero tables!);
* `.byte256` — `checkU8ByteTable` (256-row `U8Byte::check` map + tables) and
  `World.checkFunctions`;
* `.u32` — `World.checkTables` and `World.checkFunctions`;
* `.u64` — `World.checkTables`, `Gadgets.checkU64Functions`, and
  `World.checkFunctions`.

Also proves `u8ByteSpec_of_check`, giving the exact operational contract of
`U8Byte::check` directly from the 256-row table check. Zero `sorry`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedWorld

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets IxCC.AiurBackend.World
open IxCC.AiurBackend.TypedRep IxCC.AiurBackend.TypedLower

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Slim 256-Row `U8Byte::check` Table Specification & Check -/

/-- Exact map specification for `U8Byte::check(x : Field) -> ()`. -/
def U8ByteSpec (world : World F) : Prop :=
  ∀ v h r h',
    EvalFn world "U8Byte::check" [v] h r h' →
    r = .tuple [] ∧ h' = h ∧ ∃ b : Nat, b < 256 ∧ v = .field (b : F)

/-- Executable check that `U8Byte::check` is a static map over the exact 256-row
`byte_inputs` / `byte_units` tables. -/
def checkU8ByteTable (s : Generic.Source F) : Bool :=
  checkNoFunction s "U8Byte::check" &&
  checkMap s "U8Byte::check" "U8Byte::byte_inputs" "U8Byte::byte_units" &&
  checkTable s "U8Byte::byte_inputs"
    ((List.range 256).map fun (x : Nat) => .tuple [.field (x : F)]) &&
  checkTable s "U8Byte::byte_units"
    ((List.range 256).map fun (_ : Nat) => .tuple [])

/-- Executable tier-aware world check for a typed `LoweredProgram`. -/
def checkTypedWorld (s : Generic.Source F) (lp : LoweredProgram) : Bool :=
  let tablesOk := match lp.tier with
    | .none => true
    | .byte256 => checkU8ByteTable s
    | .u32 => checkTables s
    | .u64 => checkTables s && checkU64Functions s
  tablesOk && checkFunctions s lp.program

omit [Field F] [DecidableEq F] in
private theorem isPlainExpr_constantExpr :
    ∀ (c : Constant F), isPlainExpr (Generic.constantExpr c) = true
  | .field _ => by simp [Generic.constantExpr, isPlainExpr]
  | .tuple xs => by
    simp only [Generic.constantExpr, isPlainExpr, Lower.isPlainList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.tuple xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.tuple.sizeOf_spec]; omega
    exact isPlainExpr_constantExpr y
  | .construct n ctor xs => by
    simp only [Generic.constantExpr, isPlainExpr, Lower.isPlainList_iff, List.mem_map]
    rintro _ ⟨y, hy, rfl⟩
    have : sizeOf y < sizeOf (Value.construct n ctor xs) := by
      have := List.sizeOf_lt_of_mem hy
      simp [Value.construct.sizeOf_spec]; omega
    exact isPlainExpr_constantExpr y
  | .ptr _ a => Empty.elim a
termination_by c => sizeOf c

private theorem mem_zip_map_iff {α β γ : Type*} {xs : List α} {f : α → β} {g : α → γ}
    {p : β × γ} : p ∈ (xs.map f).zip (xs.map g) ↔ ∃ x ∈ xs, f x = p.1 ∧ g x = p.2 := by
  induction xs with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, h1, h2⟩)
      · exact ⟨a, Or.inl rfl, rfl, rfl⟩
      · exact ⟨x, Or.inr hx, h1, h2⟩
    · rintro ⟨x, rfl | hx, h1, h2⟩
      · left; cases p; simp_all
      · exact Or.inr ⟨x, hx, h1, h2⟩

/-- Soundness of `checkU8ByteTable`: every evaluation of `U8Byte::check` proves
its argument is a field element `(b : F)` with `b < 256` and leaves the heap
unchanged. -/
theorem u8ByteSpec_of_check {s : Generic.Source F} (h : checkU8ByteTable s = true) :
    U8ByteSpec s.world := by
  simp only [checkU8ByteTable, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hNoFn, hMap, hIn, hOut⟩ := h
  have hNoFn' := checkNoFunction_sound hNoFn
  obtain ⟨m, hm, hmIn, hmOut⟩ := checkMap_sound hMap
  obtain ⟨tIn, htIn, htInRows⟩ := checkTable_sound hIn
  obtain ⟨tOut, htOut, htOutRows⟩ := checkTable_sound hOut
  intro v heap r heap' ev
  cases ev with
  | intro prep body =>
    simp only [Generic.Source.world, sourceWorld, hNoFn', bind, Except.bind, pure, Except.pure] at prep
    cases hlook : lookupMap s.tables "U8Byte::check" [v] with
    | error e => simp [hlook] at prep
    | ok row =>
      simp only [hlook, Except.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      obtain ⟨map, key, hfm, _, _, hkey, hmem, _⟩ := Aiur.lookupMap_spec hlook
      rw [hm, Option.some.injEq] at hfm; subst hfm
      simp only [Aiur.Program.mapRows, hmIn, hmOut, htIn, htOut, htInRows, htOutRows] at hmem
      obtain ⟨b, hb, hkeq, hreq⟩ := mem_zip_map_iff.mp hmem
      have hbLt : b < 256 := List.mem_range.mp hb
      subst hkeq hreq
      simp only [Generic.constantExpr, List.map_nil] at body
      cases body with
      | tuple hargs =>
        cases hargs
        have hv := Aiur.Value.toConstant_spec hkey
        simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
          List.cons.injEq, and_true] at hv
        exact ⟨rfl, rfl, b, hbLt, hv.symm⟩
  | returned prep body =>
    simp only [Generic.Source.world, sourceWorld, hNoFn', bind, Except.bind, pure, Except.pure] at prep
    cases hlook : lookupMap s.tables "U8Byte::check" [v] with
    | error e => simp [hlook] at prep
    | ok row =>
      simp only [hlook, Except.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      exact False.elim (no_evalExit_of_plain (isPlainExpr_constantExpr row) body)

end IxCC.AiurBackend.TypedWorld
