import IxCC.Src.Word
import IxCC.Src.Syntax
import IxCC.Fir.Syntax

/-!
# The shape vocabulary (`IxCC.Shape.Basic`)

Design note: `plans/ONE-PIPELINE.md`, section 2 (statement module
`IxCCDesign.OnePipeline.Shape`).

**One vocabulary, two judgments.** A `Shape` says what is known of a value. Two judgments
read it, one per evaluator, each sound on its own, and neither is carried through a pass:

* at SrcEval a shape is a discipline: a program whose constants check against a signature is
  never stuck (the progress judgment, `IxCCCorrect.Shape*`);
* at `Fir` a shape is a fact about a value, which a back end may use and need not: the shape
  certificate (`IxCC.Fir.Shape`), checked by `Fir.Shape.check` and sound by
  `Fir.Proof.Shape.checkSound`.

The constructors are the progress judgment's (`nat`, `enum`, `data`, `irr`, `fn`, `inter`,
`any`, with the same names and arguments, so that judgment can take this type as it is) and
two more: `natLt b` (a natural below `b`: a word of width `w` is `natLt (2 ^ w)`, a checked
range is any other bound) and `arr e n` (an array of `e`, of length `n` where the length is
static). `DataDecl` is the progress judgment's table entry with the constructor identity a
parameter: a source constant at SrcEval, a constructor key at `Fir`.

A shape states a value fact, never a layout. The native layout is a function of the shape,
below (`Shape.slot`, `Shape.elemKind`, `Shape.immediate`, `Shape.rep`), together with one
condition on flows that only the native back end asks (`Shape.flowOk`); the circuit back end
reads the same shapes with its own function.

Everything here recurses structurally, so the kernel can evaluate it.
-/

set_option autoImplicit false

namespace IxCC.Shape

open IxCC.Src (CId Width)

/-- **A shape**: what is known of a value. The first seven constructors are the progress
judgment's, in its order (`IxCCCorrect.Shape2.Shape`), so its case analyses keep their goal
order when it takes this type; `natLt` and `arr` follow. -/
inductive Shape where
  /-- A `Nat` literal. -/
  | nat
  /-- A field-less constructor of the enumeration `ind`. -/
  | enum (ind : CId)
  /-- A constructor value of entry `d` of the data table, its fields at the listed shapes. -/
  | data (d : Nat)
  /-- An irrelevant position: a type, a proof, an erased argument (`□` from erasure on). -/
  | irr
  /-- A function: at SrcEval a closure typed by its code, at `Fir` a closure constructor. -/
  | fn (dom cod : Shape)
  /-- Both shapes at once (at SrcEval: a method of a dictionary used at several types). -/
  | inter (a b : Shape)
  /-- Nothing: every value has it (at SrcEval: a method nobody uses). -/
  | any
  /-- A `Nat` literal below `b`. -/
  | natLt (b : Nat)
  /-- An array whose elements have shape `elem`, of length `len` where static. -/
  | arr (elem : Shape) (len : Option Nat)
  deriving DecidableEq, Repr, Inhabited

/-- `σ₁ → … → σₙ → τ`. -/
def arrows : List Shape → Shape → Shape
  | [], τ => τ
  | σ :: σs, τ => .fn σ (arrows σs τ)

/-- The shape of a word of width `w`. -/
def Shape.word (w : Width) : Shape := .natLt w.size

/-- **One instance of a data type**: its inductive, the shapes of its parameter slots, each
constructor with the shapes of its fields in order, and whether it is a structure a projection
may read. `κ` names a constructor: `Src.CId` at SrcEval (every field, `irr` for a proof),
`Key.CtorKey` at `Fir` (kept fields only; a closure shape is a key too). -/
structure DataDecl (κ : Type) where
  ind : CId
  params : List Shape
  ctors : List (κ × List Shape)
  struct : Bool
  /-- The universe levels its constructor values carry. SrcEval's value judgment fixes them,
  since erasure reads their profile (`IxCCCorrect.ShapeTree`); `[]` at `Fir`, where levels
  are gone and nothing reads it. -/
  ls : Src.Levels := []
  deriving Repr, Inhabited

/-- **Fact weakening**, decided: every value of shape `σ` has shape `τ`. A length may be
forgotten, a bound raised, anything forgotten altogether. (Sound at `Fir` by
`Fir.Proof.Shape.leSound`.) -/
def Shape.le : Shape → Shape → Bool
  | _, .any => true
  | .natLt a, .natLt b => decide (a ≤ b)
  | .natLt _, .nat => true
  | .arr e n, .arr e' n' => Shape.le e e' && (n'.isNone || n' == n)
  | σ, τ => σ == τ

/-! ## What the native back end derives

These are functions of the shape. No certificate states them. -/

/-- The least machine width that holds every natural below `b` (8, 16, 32, 64). -/
def widthOfBound (b : Nat) : Option Width :=
  if b ≤ 2 ^ 8 then some .w8
  else if b ≤ 2 ^ 16 then some .w16
  else if b ≤ 2 ^ 32 then some .w32
  else if b ≤ 2 ^ 64 then some .w64
  else none

/-- How a position is held natively. -/
inductive NativeSlot where
  /-- One word: a tagged immediate (a natural below `2^63` as `2n + 1`, a field-less
  constructor, `□`) or the address of a cell. A natural at or above `2^63` is the address of a
  limb cell; a word at or above `2^63` that has to live here is boxed in a one-word leaf cell. -/
  | tagged
  /-- A raw machine word of the width: a register, a scalar field, a packed array element. -/
  | raw (w : Width)
  /-- Nothing: an erased position has no register. -/
  | none
  deriving DecidableEq, Repr, Inhabited

/-- The native slot of a shape: raw where a bound fits a machine width, erased where irrelevant,
one tagged word otherwise. -/
def Shape.slot : Shape → NativeSlot
  | .irr => .none
  | .natLt b =>
    match widthOfBound b with
    | some w => .raw w
    | none => .tagged
  | _ => .tagged

/-- How the elements of an array cell are stored. A cell's header names its kind, so the
release procedure reads it without any certificate. -/
inductive ElemKind where
  /-- One tagged word per element, scanned on release. -/
  | boxed
  /-- Raw elements of the width, never scanned: a leaf cell. -/
  | packed (w : Width)
  deriving DecidableEq, Repr, Inhabited

/-- The element kind of an array whose elements have shape `e`. -/
def Shape.elemKind : Shape → ElemKind
  | .natLt b =>
    match widthOfBound b with
    | some w => .packed w
    | none => .boxed
  | _ => .boxed

/-- Whether a value of the shape is never a counted cell: the ownership checker's `imm` facts
come from here (and from nowhere else once `Nat` is arbitrary precision). A raw word and an
erased position hold no reference; an enumeration value is a tagged immediate. -/
def Shape.immediate : Shape → Bool
  | .irr | .enum _ => true
  | .natLt b => (widthOfBound b).isSome
  | _ => false

/-- **A flow the native back end takes at no cost or at the cost of one box or unbox.** The
shape checker allows every weakening; the native back end additionally asks this of each flow
(an argument to a parameter, a value to a field or a join parameter, a result to its binder),
and declines otherwise. An array keeps its element kind along every flow, and reaches a
position of unknown shape only when its kind is `boxed`: phase 1 has no dynamic dispatch on the
kind and no implicit copy of an array (design note, section 2.5, for the relaxation). -/
def Shape.flowOk : Shape → Shape → Bool
  | .arr e _, .arr e' _ => e.elemKind == e'.elemKind && Shape.flowOk e e'
  | .arr e _, _ => e.elemKind == .boxed
  | _, _ => true

/-- The representation `Fir.Rep` elaborates the shape at: a raw word where the bound fits 64
bits, one tagged word otherwise. A derived quantity: `Fir.Rep.elaborate` inserts `box` and
`unbox` from it (`Fir.Rep.ofShapes`). -/
def Shape.rep : Shape → Fir.Rep
  | .natLt b => if b ≤ 2 ^ 64 then .word else .tobj
  | _ => .tobj

/-! ## Small facts -/

theorem Shape.le_any (σ : Shape) : σ.le .any = true := by
  cases σ <;> simp [Shape.le]

/-- Weakening is reflexive. -/
theorem Shape.le_refl (σ : Shape) : σ.le σ = true := by
  induction σ with
  | arr e n ih => simp [Shape.le, ih]
  | _ => simp [Shape.le]

/-- A word of a width is held raw at that width. -/
theorem Shape.word_slot (w : Width) : (Shape.word w).slot = .raw w := by
  cases w <;> first | rfl | decide

/-- An array of words of a width is packed at that width. -/
theorem Shape.word_elemKind (w : Width) : (Shape.word w).elemKind = .packed w := by
  cases w <;> first | rfl | decide

/-- A word is never a counted cell where its shape is known. -/
theorem Shape.word_immediate (w : Width) : (Shape.word w).immediate = true := by
  cases w <;> first | rfl | decide

/-- A word of any width elaborates raw. -/
theorem Shape.word_rep (w : Width) : (Shape.word w).rep = .word := by
  cases w <;> first | rfl | decide

end IxCC.Shape
