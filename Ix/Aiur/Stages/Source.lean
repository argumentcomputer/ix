module
public import Std.Data.HashSet.Basic
public import Ix.Aiur.Goldilocks
public import Ix.IndexMap

/-!
Stage 1 (Source) IR — the post-elaboration term language.

The `Data` mutual child has been flattened into direct `Term.tuple` /
`Term.array` constructors to give cleaner induction principles.
-/

public section
@[expose] section

namespace Aiur

inductive Local
  | str : String → Local
  | idx : Nat → Local
  deriving Repr, Inhabited, Hashable

instance : BEq Local where
  beq
    | .str s₁, .str s₂ => s₁ == s₂
    | .idx n₁, .idx n₂ => n₁ == n₂
    | _, _ => false

structure Global where
  toName : Lean.Name
  deriving Repr, BEq, Inhabited

instance : EquivBEq Global where
  symm {_ _} h := by rw [BEq.beq] at h ⊢; exact BEq.symm h
  trans {_ _ _} h₁ h₂ := by rw [BEq.beq] at h₁ h₂ ⊢; exact BEq.trans h₁ h₂
  rfl {_} := by rw [BEq.beq]; apply BEq.rfl

instance : Hashable Global where
  hash a := hash a.toName

instance : LawfulHashable Global where
  hash_eq a b h := LawfulHashable.hash_eq a.toName b.toName h

instance : ToString Global where
  toString g := g.toName.toString

def Global.init (limb : String) : Global :=
  ⟨.mkSimple limb⟩

def Global.pushNamespace (global : Global) (limb : String) : Global :=
  ⟨global.toName.mkStr limb⟩

def Global.popNamespace (global : Global) : Option (String × Global) :=
  match global.toName with
  | .str tail head => some (head, ⟨tail⟩)
  | _ => none

inductive Typ where
  | unit
  | field
  /-- A field element known to be range-checked into `[0, 256)`. Same runtime
  representation as `field`; the distinction is erased after type-checking
  (`Concretize` collapses `u8` to `field`). -/
  | u8
  | tuple : Array Typ → Typ
  | array : Typ → Nat → Typ
  | pointer : Typ → Typ
  | ref : Global → Typ
  | app : Global → Array Typ → Typ
  | function : List Typ → Typ → Typ
  | mvar : Nat → Typ
  deriving Repr, Hashable, Inhabited

deriving instance DecidableEq for Global

instance : LawfulBEq Global where
  eq_of_beq {a b} h := by
    rw [BEq.beq] at h
    have : a.toName = b.toName := eq_of_beq h
    cases a; cases b; congr
  rfl {a} := by rw [BEq.beq]; exact BEq.rfl

/-! ### Custom `BEq Typ` + `LawfulBEq Typ`

`deriving BEq` on nested inductives produces an opaque `beq` function that
can't be unfolded in proofs. We instead define `Typ.beq` explicitly via
well-founded recursion on `sizeOf`, then prove it decides propositional
equality. `EquivBEq Typ` and `LawfulHashable Typ` follow from the stdlib
low-priority instances `[LawfulBEq α] → EquivBEq α` and
`[LawfulBEq α] → LawfulHashable α`.
-/

namespace Typ

/-- Structural boolean equality on `Typ`. Pairwise-compares nested `Array Typ`
and `List Typ` positions via `sizeOf` termination. -/
def beq : Typ → Typ → Bool
  | .unit, .unit => true
  | .field, .field => true
  | .u8, .u8 => true
  | .tuple ts, .tuple ts' =>
    if hsz : ts.size = ts'.size then
      (List.finRange ts.size).all fun i =>
        beq (ts[i.val]'i.isLt) (ts'[i.val]'(hsz ▸ i.isLt))
    else false
  | .array t n, .array t' n' => beq t t' && n == n'
  | .pointer t, .pointer t' => beq t t'
  | .ref g, .ref g' => g == g'
  | .app g args, .app g' args' =>
    (g == g') &&
      (if hsz : args.size = args'.size then
        (List.finRange args.size).all fun i =>
          beq (args[i.val]'i.isLt) (args'[i.val]'(hsz ▸ i.isLt))
      else false)
  | .function ins out, .function ins' out' =>
    beq out out' && listBeqAux ins ins'
  | .mvar n, .mvar n' => n == n'
  | _, _ => false
where
  /-- Helper: pairwise equality on `List Typ`. Inlined into `Typ.beq` to stay
  within a single well-founded recursion on `sizeOf`. -/
  listBeqAux : List Typ → List Typ → Bool
    | [], [] => true
    | _ :: _, [] => false
    | [], _ :: _ => false
    | t :: rest, t' :: rest' => beq t t' && listBeqAux rest rest'

/-- Reflexivity of `Typ.beq` via the generated three-motive recursor.
We use a strengthened list motive so it supplies element-wise refl. -/
theorem beq_refl (a : Typ) : beq a a = true := by
  refine
    @Typ.rec
      (fun a => beq a a = true)
      (fun as => ∀ (i : Nat) (h : i < as.size), beq (as[i]'h) (as[i]'h) = true)
      (fun ts => beq.listBeqAux ts ts = true ∧
                 ∀ (i : Nat) (h : i < ts.length), beq (ts[i]'h) (ts[i]'h) = true)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  -- case .unit
  · unfold beq; rfl
  -- case .field
  · unfold beq; rfl
  -- case .u8
  · unfold beq; rfl
  -- case .tuple ts ih
  · intro ts ih
    unfold beq
    simp only [↓reduceDIte]
    rw [List.all_eq_true]
    intro i _
    exact ih i.val i.isLt
  -- case .array t n iht
  · intro t n iht
    unfold beq
    simp only [Bool.and_eq_true]
    exact ⟨iht, by simp⟩
  -- case .pointer t iht
  · intro t iht
    unfold beq
    exact iht
  -- case .ref g
  · intro g
    unfold beq
    simp
  -- case .app g args ih
  · intro g args ih
    unfold beq
    simp only [Bool.and_eq_true]
    refine ⟨by simp, ?_⟩
    simp only [↓reduceDIte]
    rw [List.all_eq_true]
    intro i _
    exact ih i.val i.isLt
  -- case .function ins out ihList ihOut
  · intro ins out ihList ihOut
    unfold beq
    simp only [Bool.and_eq_true]
    exact ⟨ihOut, ihList.1⟩
  -- case .mvar n
  · intro n
    unfold beq
    simp
  -- Array.mk case
  · intro ts ih
    intro i h
    have hAcc : (⟨ts⟩ : Array Typ)[i]'h = ts[i]'h := rfl
    rw [hAcc]
    exact ih.2 i h
  -- List.nil
  · refine ⟨?_, ?_⟩
    · unfold beq.listBeqAux; rfl
    · intro i h; simp at h
  -- List.cons hd tl ihHd ihTl
  · intro hd tl ihHd ihTl
    refine ⟨?_, ?_⟩
    · unfold beq.listBeqAux
      simp only [Bool.and_eq_true]
      exact ⟨ihHd, ihTl.1⟩
    · intro i h
      cases i with
      | zero => exact ihHd
      | succ k =>
        have hk : k < tl.length := by simp [List.length] at h; omega
        exact ihTl.2 k hk

/-- Converse: `beq a b = true → a = b`. Same three-motive recursion. -/
theorem eq_of_beq {a b : Typ} (h : beq a b = true) : a = b := by
  revert b h
  refine
    @Typ.rec
      (fun a => ∀ b, beq a b = true → a = b)
      (fun as => ∀ (i : Nat) (h₁ : i < as.size) (t' : Typ),
        beq (as[i]'h₁) t' = true → (as[i]'h₁) = t')
      (fun ts => (∀ (ts' : List Typ), beq.listBeqAux ts ts' = true → ts = ts') ∧
                 (∀ (i : Nat) (h : i < ts.length) (t' : Typ),
                    beq (ts[i]'h) t' = true → (ts[i]'h) = t'))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  -- case .unit
  · intro b h
    cases b <;> (unfold beq at h; first | rfl | cases h)
  -- case .field
  · intro b h
    cases b <;> (unfold beq at h; first | rfl | cases h)
  -- case .u8
  · intro b h
    cases b <;> (unfold beq at h; first | rfl | cases h)
  -- case .tuple ts ih
  · intro ts ih b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i ts'
    unfold beq at h
    split at h
    · rename_i hsz
      rw [List.all_eq_true] at h
      apply congrArg
      apply Array.ext (h₁ := hsz)
      intro i hi₁ hi₂
      have hmem : ⟨i, hi₁⟩ ∈ List.finRange ts.size := List.mem_finRange _
      have hib := h ⟨i, hi₁⟩ hmem
      exact ih i hi₁ (ts'[i]'hi₂) hib
    · cases h
  -- case .array t n iht
  · intro t n iht b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i t' n'
    unfold beq at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨ht, hn⟩ := h
    have := iht t' ht
    subst this; subst hn; rfl
  -- case .pointer t iht
  · intro t iht b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i t'
    unfold beq at h
    have := iht t' h
    subst this; rfl
  -- case .ref g
  · intro g b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i g'
    unfold beq at h
    have : g = g' := beq_iff_eq.mp h
    subst this; rfl
  -- case .app g args ih
  · intro g args ih b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i g' args'
    unfold beq at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hg, ha⟩ := h
    have hgeq : g = g' := beq_iff_eq.mp hg
    subst hgeq
    split at ha
    · rename_i hsz
      rw [List.all_eq_true] at ha
      apply congrArg
      apply Array.ext (h₁ := hsz)
      intro i hi₁ hi₂
      have hmem : ⟨i, hi₁⟩ ∈ List.finRange args.size := List.mem_finRange _
      have hib := ha ⟨i, hi₁⟩ hmem
      exact ih i hi₁ (args'[i]'hi₂) hib
    · cases ha
  -- case .function ins out ihList ihOut
  · intro ins out ihList ihOut b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i ins' out'
    unfold beq at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hout, hins⟩ := h
    have := ihOut out' hout
    subst this
    have := ihList.1 ins' hins
    subst this; rfl
  -- case .mvar n
  · intro n b h
    cases b <;> (try (unfold beq at h; cases h))
    rename_i n'
    unfold beq at h
    have : n = n' := beq_iff_eq.mp h
    subst this; rfl
  -- Array.mk case (motive_2)
  · intro ts ih
    intro i h₁ t' h
    have hAcc : (⟨ts⟩ : Array Typ)[i]'h₁ = ts[i]'h₁ := rfl
    rw [hAcc] at *
    exact ih.2 i h₁ t' h
  -- List.nil (motive_3)
  · refine ⟨?_, ?_⟩
    · intro ts' h
      cases ts' with
      | nil => rfl
      | cons _ _ => unfold beq.listBeqAux at h; cases h
    · intro i h _ _; simp at h
  -- List.cons hd tl ihHd ihTl (motive_3)
  · intro hd tl ihHd ihTl
    refine ⟨?_, ?_⟩
    · intro ts' h
      cases ts' with
      | nil => unfold beq.listBeqAux at h; cases h
      | cons hd' tl' =>
        unfold beq.listBeqAux at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨ht, hr⟩ := h
        have := ihHd hd' ht
        subst this
        have := ihTl.1 tl' hr
        subst this; rfl
    · intro i h t' hb
      cases i with
      | zero => exact ihHd t' hb
      | succ k =>
        have hk : k < tl.length := by simp [List.length] at h; omega
        exact ihTl.2 k hk t' hb

/-- Does `t` contain any `.pointer` subterm? Used to forbid pointer types in
the signatures of `entry = true` (public) functions. -/
def hasPointer : Typ → Bool
  | .unit | .field | .u8 | .ref _ | .mvar _ => false
  | .pointer _ => true
  | .tuple ts => ts.attach.any fun ⟨t, _⟩ => hasPointer t
  | .array t _ => hasPointer t
  | .app _ args => args.attach.any fun ⟨t, _⟩ => hasPointer t
  | .function ins out =>
    hasPointer out || ins.attach.any fun ⟨t, _⟩ => hasPointer t
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

end Typ

instance : BEq Typ := ⟨Typ.beq⟩

instance : LawfulBEq Typ where
  eq_of_beq := Typ.eq_of_beq
  rfl := Typ.beq_refl _

instance : EquivBEq Typ := inferInstance

instance : LawfulHashable Typ := inferInstance

inductive Pattern
  | var : Local → Pattern
  | wildcard : Pattern
  | ref : Global → List Pattern → Pattern
  | field : G → Pattern
  | tuple : Array Pattern → Pattern
  | array : Array Pattern → Pattern
  | or : Pattern → Pattern → Pattern
  | pointer : Pattern → Pattern
  deriving Repr, BEq, Hashable, Inhabited

namespace Source

/-- How a function application is compiled.
* `normal` — a constrained circuit call (its own circuit, a lookup, and
  output columns at the call site).
* `unconstrained` — a call whose callee is trusted (no lookup / circuit
  constraint); the old `unconstrained := true`.
* `inlined` — request that the callee's body be spliced into the caller.
  Callees with explicit returns retain a normal function-call boundary.
  Eliminated by
  `Toplevel.inlineCalls` before typechecking; forbidden for callees that
  are (transitively) inline-recursive. -/
inductive CallMode
  | normal
  | unconstrained
  | inlined
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-- Stage 1 term language. `tuple` and `array` are direct constructors (no `Data`
mutual child); cf. `Ix/Aiur/Term.lean` which nested them under `.data`. -/
inductive Term
  | unit
  | var : Local → Term
  | ref : Global → Term
  | field : G → Term
  | tuple : Array Term → Term
  | array : Array Term → Term
  | ret : Term → Term
  | let : Pattern → Term → Term → Term
  | match : Term → List (Pattern × Term) → Term
  | app : Global → List Term → (mode : CallMode) → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | mul : Term → Term → Term
  | eqZero : Term → Term
  | proj : Term → Nat → Term
  | get : Term → Nat → Term
  | slice : Term → Nat → Nat → Term
  | set : Term → Nat → Term → Term
  | store : Term → Term
  | load : Term → Term
  | ptrVal : Term → Term
  | ann : Typ → Term → Term
  | assertEq : Term → Term → (msg : Option String) → (ret : Term) → Term
  | ioGetInfo : (channel : Term) → (key : Term) → Term
  | ioSetInfo : (channel : Term) → (key : Term) → (idx : Term) → (len : Term) → (ret : Term) → Term
  | ioRead : (channel : Term) → (idx : Term) → (len : Nat) → Term
  | ioWrite : (channel : Term) → (data : Term) → (ret : Term) → Term
  | u8BitDecomposition : Term → Term
  | u8ShiftLeft : Term → Term
  | u8ShiftRight : Term → Term
  | u8Xor : Term → Term → Term
  | u8Add : Term → Term → Term
  | u8Mul : Term → Term → Term
  | u8Sub : Term → Term → Term
  | u8And : Term → Term → Term
  | u8Or : Term → Term → Term
  | u8LessThan : Term → Term → Term
  | u32LessThan : Term → Term → Term
  | u8XorSplit7 : Term → Term → Term
  | u8XorSplit4 : Term → Term → Term
  /-- Native unconstrained u32 addition hint. The four result bytes are fresh
  advice; the carry is a virtual value derived from the packed operands. -/
  | unconstrainedU32Add : Term → Term → Term
  /-- Native unconstrained three-input u32 addition hint. -/
  | unconstrainedU32Add3 : Term → Term → Term → Term
  /-- Pack four little-endian bytes into a field value. This is a virtual
  linear expression and does not allocate an auxiliary column. -/
  | u32ToField : Term → Term
  /-- Unconstrained LE byte-list division-modulo hint. Inputs are two
  `List<U64>` (klimbs) values (LE limb order). Output is a tuple of two
  fresh `List<U64>` values `(q, r)` with `q*b + r = a` and `0 ≤ r < b`
  (when `b > 0`). Computed natively by the Aiur runtime via BigUint
  div_rem; no constraints generated and no per-step memo growth. The
  caller must verify `q*b + r == a` and `r < b` in constrained code. -/
  | unconstrainedBigUintDivMod : (a : Term) → (b : Term) → Term
  /-- Unconstrained hint: the 8 little-endian bytes of a field element's
  canonical `u64` value, as a `[G; 8]` — advice must not type as
  range-checked bytes. Computed natively by the Aiur runtime; no
  constraints generated. The caller must range-check each byte (minting
  the `u8`s from the check outputs), assert they recompose to the input
  (`Σ bᵢ·256ⁱ == x`), and assert canonicality (`< p`) in constrained
  code; together these pin the unique canonical decomposition. -/
  | unconstrainedGToBytes : Term → Term
  /-- Unconstrained hint: the field inverse of a field element (`0 ↦ 0`).
  Computed natively by the Aiur runtime; no constraints generated — the
  caller must pin it, e.g. via `t = x·i − 1; assert x·t == 0;
  assert i·t == 0` (forces `i = x⁻¹` when `x ≠ 0` and `i = 0` otherwise). -/
  | unconstrainedGInverse : Term → Term
  /-- A `U8` literal in `[0, 256)`. Lowered to a plain field constant of type
  `u8` (no range-check lookup, since the value is statically in range). -/
  | u8Lit : Nat → Term
  /-- Range-check two field elements into `[0, 256)`, producing two `u8`s.
  Pairs because the byte chip already takes two elements per lookup row. -/
  | u8RangeCheck : Term → Term → Term
  /-- Forget that a `u8` was range-checked, recovering the underlying `G`. -/
  | toField : Term → Term
  /-- Reinterpret a `G` as a `u8` *without* a range check. Unsafe: the caller
  asserts the value is already in `[0, 256)` (e.g. a sum of bytes known not to
  overflow). Cheaper than `u8_range_check` since it adds no lookup. -/
  | u8FromFieldUnsafe : Term → Term
  | debug : String → Option Term → Term → Term
  deriving Repr, BEq, Hashable, Inhabited

end Source

structure Constructor where
  nameHead : String
  argTypes : List Typ
  deriving Repr, BEq, Inhabited

structure DataType where
  name : Global
  params : List String
  constructors : List Constructor
  deriving Repr, BEq, Inhabited

structure TypeAlias where
  name : Global
  params : List String
  expansion : Typ
  deriving Repr, BEq, Inhabited

namespace Source

/-- `true` iff none of `inputs` nor `output` contain a `.pointer` subterm.
Used to enforce that public entry functions expose no pointer-typed values. -/
def sigPointerFree (inputs : List (Local × Typ)) (output : Typ) : Bool :=
  !output.hasPointer && inputs.all (fun ⟨_, t⟩ => !t.hasPointer)

structure Function where
  name : Global
  params : List String
  inputs : List (Local × Typ)
  output : Typ
  body : Term
  entry : Bool
  /-- Polymorphic public entry points are forbidden by construction:
  either the function is monomorphic (`params = []`) or not public
  (`entry = false`). -/
  entryMonomorphic : params = [] ∨ entry = false := by
    first | exact Or.inl rfl | exact Or.inr rfl
  /-- Public entry points cannot expose pointer-typed values: either the
  signature is pointer-free or the function is not public (`entry = false`). -/
  entryPointerFree : sigPointerFree inputs output = true ∨ entry = false := by
    first | exact Or.inl rfl | exact Or.inr rfl
  deriving Repr

instance : Inhabited Function where
  default :=
    { name := default, params := [], inputs := default, output := default,
      body := default, entry := default,
      entryMonomorphic := Or.inl rfl,
      entryPointerFree := Or.inr rfl }

/-- Smart constructor for non-entry monomorphic functions. -/
def Function.monoNonEntry (name : Global) (inputs : List (Local × Typ))
    (output : Typ) (body : Term) : Function :=
  { name, params := [], inputs, output, body, entry := false,
    entryMonomorphic := Or.inl rfl, entryPointerFree := Or.inr rfl }

/-- Smart constructor for public entry functions. Requires a proof that the
signature contains no pointer types. -/
def Function.monoEntry (name : Global) (inputs : List (Local × Typ))
    (output : Typ) (body : Term)
    (h : sigPointerFree inputs output = true) : Function :=
  { name, params := [], inputs, output, body, entry := true,
    entryMonomorphic := Or.inl rfl, entryPointerFree := Or.inl h }

/-- Smart constructor for polymorphic functions (`entry = false` forced). -/
def Function.poly (name : Global) (params : List String) (inputs : List (Local × Typ))
    (output : Typ) (body : Term) : Function :=
  { name, params, inputs, output, body, entry := false,
    entryMonomorphic := Or.inr rfl, entryPointerFree := Or.inr rfl }

structure Toplevel where
  dataTypes : Array DataType
  typeAliases : Array TypeAlias
  functions : Array Function
  deriving Repr

def Toplevel.getFuncIdx (toplevel : Toplevel) (funcName : Lean.Name) : Option Nat := do
  toplevel.functions.findIdx? fun function => function.name.toName == funcName

def Toplevel.merge (x y : Toplevel) : Except Global Toplevel := do
  let ⟨xDT, xTA, xF⟩ := x
  let ⟨yDT, yTA, yF⟩ := y
  let (globals, dataTypes) ← mergeArrays DataType.name ∅ xDT yDT
  let (globals, typeAliases) ← mergeArrays TypeAlias.name globals xTA yTA
  let (_, functions) ← mergeArrays Function.name globals xF yF
  pure ⟨dataTypes, typeAliases, functions⟩
where
  mergeArrays {α : Type} (getName : α → Global) (globals : Std.HashSet Global)
      (xs ys : Array α) : Except Global (Std.HashSet Global × Array α) := do
    let mut globals := globals
    let mut result := Array.emptyWithCapacity (xs.size + ys.size)
    for set in [xs, ys] do
      for item in set do
        let n := getName item
        if globals.contains n then throw n
        globals := globals.insert n
        result := result.push item
    pure (globals, result)

/-- Allocate one fresh name per binder in a pattern. Alternative arms
reuse the same renaming for names they bind in common. -/
def Pattern.freshenBindings (stem : String) (cnt : Nat) (subst : Std.HashMap Local Local) :
    Pattern → Nat × Std.HashMap Local Local × Pattern
  | .var x =>
    if let some x' := subst[x]? then (cnt, subst, .var x') else
    let x' : Local := .str (stem ++ toString cnt)
    (cnt + 1, subst.insert x x', .var x')
  | .wildcard => (cnt, subst, .wildcard)
  | .field g => (cnt, subst, .field g)
  | .ref g ps =>
    let (cnt, subst, ps') := ps.attach.foldl (init := (cnt, subst, ([] : List Pattern)))
      fun (cnt, subst, acc) ⟨p, _⟩ =>
        let (cnt, subst, p') := Pattern.freshenBindings stem cnt subst p
        (cnt, subst, acc ++ [p'])
    (cnt, subst, .ref g ps')
  | .tuple ps =>
    let (cnt, subst, ps') := ps.attach.foldl (init := (cnt, subst, (#[] : Array Pattern)))
      fun (cnt, subst, acc) ⟨p, _⟩ =>
        let (cnt, subst, p') := Pattern.freshenBindings stem cnt subst p
        (cnt, subst, acc.push p')
    (cnt, subst, .tuple ps')
  | .array ps =>
    let (cnt, subst, ps') := ps.attach.foldl (init := (cnt, subst, (#[] : Array Pattern)))
      fun (cnt, subst, acc) ⟨p, _⟩ =>
        let (cnt, subst, p') := Pattern.freshenBindings stem cnt subst p
        (cnt, subst, acc.push p')
    (cnt, subst, .array ps')
  | .or p q =>
    let (cnt, subst, p') := Pattern.freshenBindings stem cnt subst p
    let (cnt, subst, q') := Pattern.freshenBindings stem cnt subst q
    (cnt, subst, .or p' q')
  | .pointer p =>
    let (cnt, subst, p') := Pattern.freshenBindings stem cnt subst p
    (cnt, subst, .pointer p')
termination_by p => sizeOf p
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)


def Pattern.freshenWith (stem : String) (cnt : Nat)
    (subst : Std.HashMap Local Local) (pattern : Pattern) :
    Nat × Std.HashMap Local Local × Pattern :=
  let (cnt, names, pattern) := Pattern.freshenBindings stem cnt ∅ pattern
  (cnt, names.fold (init := subst) (fun subst old fresh => subst.insert old fresh), pattern)

def renameLocalCall (subst : Std.HashMap Local Local) (global : Global) : Global :=
  match global.toName with
  | .str .anonymous name =>
    match subst[Local.str name]? with
    | some (.str fresh) => Global.init fresh
    | _ => global
  | _ => global

def Term.freshenWith (stem : String) (cnt : Nat) (subst : Std.HashMap Local Local) :
    Term → Nat × Term :=
  fun t =>
  match t with
  | .var x => (cnt, .var (subst.getD x x))
  | .unit | .ref _ | .field _ | .u8Lit _ => (cnt, t)
  | .let p v b =>
    let (cnt, v') := Term.freshenWith stem cnt subst v
    let (cnt, subst', p') := Pattern.freshenWith stem cnt subst p
    let (cnt, b') := Term.freshenWith stem cnt subst' b
    (cnt, .let p' v' b')
  | .match s arms =>
    let (cnt, s') := Term.freshenWith stem cnt subst s
    let (cnt, arms') := arms.attach.foldl (init := (cnt, ([] : List (Pattern × Term))))
      fun (cnt, acc) ⟨(p, a), _⟩ =>
        let (cnt, subst', p') := Pattern.freshenWith stem cnt subst p
        let (cnt, a') := Term.freshenWith stem cnt subst' a
        (cnt, acc ++ [(p', a')])
    (cnt, .match s' arms')
  | .tuple ts =>
    let (cnt, ts') := ts.attach.foldl (init := (cnt, #[])) fun (cnt, acc) ⟨x, _⟩ =>
      let (cnt, x') := Term.freshenWith stem cnt subst x; (cnt, acc.push x')
    (cnt, .tuple ts')
  | .array ts =>
    let (cnt, ts') := ts.attach.foldl (init := (cnt, #[])) fun (cnt, acc) ⟨x, _⟩ =>
      let (cnt, x') := Term.freshenWith stem cnt subst x; (cnt, acc.push x')
    (cnt, .array ts')
  | .app g args mode =>
    let (cnt, args') := args.attach.foldl (init := (cnt, ([] : List Term))) fun (cnt, acc) ⟨x, _⟩ =>
      let (cnt, x') := Term.freshenWith stem cnt subst x; (cnt, acc ++ [x'])
    (cnt, .app (renameLocalCall subst g) args' mode)
  | .ret a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .ret a')
  | .add a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .add a' b')
  | .sub a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .sub a' b')
  | .mul a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .mul a' b')
  | .eqZero a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .eqZero a')
  | .proj a n => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .proj a' n)
  | .get a n => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .get a' n)
  | .slice a i j => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .slice a' i j)
  | .set a n v => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, v') := Term.freshenWith stem cnt subst v; (cnt, .set a' n v')
  | .store a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .store a')
  | .load a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .load a')
  | .ptrVal a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .ptrVal a')
  | .ann τ a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .ann τ a')
  | .assertEq a b msg c =>
    let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; let (cnt, c') := Term.freshenWith stem cnt subst c
    (cnt, .assertEq a' b' msg c')
  | .ioGetInfo c k => let (cnt, c') := Term.freshenWith stem cnt subst c; let (cnt, k') := Term.freshenWith stem cnt subst k; (cnt, .ioGetInfo c' k')
  | .ioSetInfo c k i l rv =>
    let (cnt, c') := Term.freshenWith stem cnt subst c; let (cnt, k') := Term.freshenWith stem cnt subst k; let (cnt, i') := Term.freshenWith stem cnt subst i
    let (cnt, l') := Term.freshenWith stem cnt subst l; let (cnt, rv') := Term.freshenWith stem cnt subst rv
    (cnt, .ioSetInfo c' k' i' l' rv')
  | .ioRead c i n => let (cnt, c') := Term.freshenWith stem cnt subst c; let (cnt, i') := Term.freshenWith stem cnt subst i; (cnt, .ioRead c' i' n)
  | .ioWrite c d rv =>
    let (cnt, c') := Term.freshenWith stem cnt subst c; let (cnt, d') := Term.freshenWith stem cnt subst d; let (cnt, rv') := Term.freshenWith stem cnt subst rv
    (cnt, .ioWrite c' d' rv')
  | .u8BitDecomposition a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .u8BitDecomposition a')
  | .u8ShiftLeft a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .u8ShiftLeft a')
  | .u8ShiftRight a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .u8ShiftRight a')
  | .u8Xor a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8Xor a' b')
  | .u8Add a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8Add a' b')
  | .u8Mul a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8Mul a' b')
  | .u8Sub a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8Sub a' b')
  | .u8And a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8And a' b')
  | .u8Or a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8Or a' b')
  | .u8LessThan a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8LessThan a' b')
  | .u32LessThan a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u32LessThan a' b')
  | .u8XorSplit7 a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8XorSplit7 a' b')
  | .u8XorSplit4 a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8XorSplit4 a' b')
  | .unconstrainedU32Add a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .unconstrainedU32Add a' b')
  | .unconstrainedU32Add3 a b c => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; let (cnt, c') := Term.freshenWith stem cnt subst c; (cnt, .unconstrainedU32Add3 a' b' c')
  | .u32ToField a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .u32ToField a')
  | .unconstrainedBigUintDivMod a b =>
    let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .unconstrainedBigUintDivMod a' b')
  | .u8RangeCheck a b => let (cnt, a') := Term.freshenWith stem cnt subst a; let (cnt, b') := Term.freshenWith stem cnt subst b; (cnt, .u8RangeCheck a' b')
  | .toField a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .toField a')
  | .u8FromFieldUnsafe a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .u8FromFieldUnsafe a')
  | .unconstrainedGToBytes a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .unconstrainedGToBytes a')
  | .unconstrainedGInverse a => let (cnt, a') := Term.freshenWith stem cnt subst a; (cnt, .unconstrainedGInverse a')
  | .debug s o a =>
    let (cnt, o') := match o with
      | none => (cnt, none)
      | some x => let (cnt, x') := Term.freshenWith stem cnt subst x; (cnt, some x')
    let (cnt, a') := Term.freshenWith stem cnt subst a
    (cnt, .debug s o' a')
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)


/-- Freshen an inlined pattern with the inline-expansion name stem. -/
def Pattern.freshen (cnt : Nat) (subst : Std.HashMap Local Local) (pattern : Pattern) :
    Nat × Std.HashMap Local Local × Pattern :=
  Pattern.freshenWith "inl#" cnt subst pattern

/-- Freshen an inlined body, including local function-call names. -/
def Term.freshen (cnt : Nat) (subst : Std.HashMap Local Local) (term : Term) : Nat × Term :=
  Term.freshenWith "inl#" cnt subst term

/-- Peel the leading `let` bindings off a term: returns the binding frames
(outermost first) and the non-`let` core. -/
def Term.peelLets : Term → List (Pattern × Term) × Term
  | .let p v b => let (fs, c) := Term.peelLets b; ((p, v) :: fs, c)
  | t => ([], t)

/-- Wrap `body` in a chain of `let` frames (first frame outermost). -/
def Term.wrapLets : List (Pattern × Term) → Term → Term
  | [], body => body
  | (p, v) :: fs, body => .let p v (Term.wrapLets fs body)

/-- Every `.inlined` call site in `t`, as `(callee, argCount)` pairs. Drives
both validation (callee exists, arity matches) and the inline-dependency
graph the bottom-up expansion is ordered by. -/
def Term.inlineCallSites : Term → List (Global × Nat)
  | .app g args .inlined =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ a.inlineCallSites) [(g, args.length)]
  | .app _ args _ =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ a.inlineCallSites) []
  | .unit | .var _ | .ref _ | .field _ | .u8Lit _ => []
  | .tuple ts | .array ts =>
    ts.attach.foldl (fun acc ⟨a, _⟩ => acc ++ a.inlineCallSites) []
  | .match s arms =>
    arms.attach.foldl (fun acc ⟨(_, a), _⟩ => acc ++ a.inlineCallSites) s.inlineCallSites
  | .let _ v b => v.inlineCallSites ++ b.inlineCallSites
  | .add a b | .sub a b | .mul a b | .set a _ b
  | .u8Xor a b | .u8Add a b | .u8Mul a b | .u8Sub a b | .u8And a b | .u8Or a b
  | .u8LessThan a b | .u32LessThan a b | .u8XorSplit7 a b | .u8XorSplit4 a b | .unconstrainedU32Add a b
  | .unconstrainedBigUintDivMod a b | .u8RangeCheck a b | .ioGetInfo a b =>
    a.inlineCallSites ++ b.inlineCallSites
  | .assertEq a b _ c => a.inlineCallSites ++ b.inlineCallSites ++ c.inlineCallSites
  | .ioWrite a b c => a.inlineCallSites ++ b.inlineCallSites ++ c.inlineCallSites
  | .ioSetInfo c k i l rv =>
    c.inlineCallSites ++ k.inlineCallSites ++ i.inlineCallSites ++ l.inlineCallSites ++ rv.inlineCallSites
  | .ioRead a b _ => a.inlineCallSites ++ b.inlineCallSites
  | .ret a | .eqZero a | .proj a _ | .get a _ | .slice a _ _ | .store a | .load a
  | .ptrVal a | .ann _ a | .u8BitDecomposition a | .u8ShiftLeft a | .u8ShiftRight a
  | .toField a | .u8FromFieldUnsafe a
  | .unconstrainedGToBytes a | .unconstrainedGInverse a => a.inlineCallSites
  | .u32ToField a => a.inlineCallSites
  | .unconstrainedU32Add3 a b c => a.inlineCallSites ++ b.inlineCallSites ++ c.inlineCallSites
  | .debug _ o a => (match o with | none => [] | some x => x.inlineCallSites) ++ a.inlineCallSites
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Explicit returns require a function-call boundary when considering
inlining. Splicing them would let a callee return from its caller. -/
def Term.hasExplicitReturn : Term → Bool
  | .ret _ => true
  | .var _ | .unit | .field _ | .u8Lit _ | .ref _ => false
  | .app _ args _ => args.attach.any fun arg => Term.hasExplicitReturn arg.val
  | .tuple terms | .array terms => terms.attach.any fun term => Term.hasExplicitReturn term.val
  | .let _ value body => Term.hasExplicitReturn value || Term.hasExplicitReturn body
  | .match scrut arms => Term.hasExplicitReturn scrut ||
      arms.attach.any fun arm => Term.hasExplicitReturn arm.val.2
  | .eqZero a | .proj a _ | .get a _ | .slice a _ _
  | .store a | .load a | .ptrVal a | .ann _ a
  | .u8BitDecomposition a | .u8ShiftLeft a | .u8ShiftRight a
  | .u32ToField a | .unconstrainedGToBytes a | .unconstrainedGInverse a
  | .toField a | .u8FromFieldUnsafe a => Term.hasExplicitReturn a
  | .add a b | .sub a b | .mul a b | .set a _ b | .ioGetInfo a b | .ioRead a b _
  | .u8Xor a b | .u8Add a b | .u8Mul a b | .u8Sub a b | .u8And a b | .u8Or a b
  | .u8LessThan a b | .u32LessThan a b | .u8XorSplit7 a b | .u8XorSplit4 a b
  | .unconstrainedU32Add a b | .unconstrainedBigUintDivMod a b | .u8RangeCheck a b =>
    Term.hasExplicitReturn a || Term.hasExplicitReturn b
  | .assertEq a b _ c | .ioWrite a b c | .unconstrainedU32Add3 a b c =>
    Term.hasExplicitReturn a || Term.hasExplicitReturn b || Term.hasExplicitReturn c
  | .ioSetInfo a b c d e => Term.hasExplicitReturn a || Term.hasExplicitReturn b ||
      Term.hasExplicitReturn c || Term.hasExplicitReturn d || Term.hasExplicitReturn e
  | .debug _ none continuation => Term.hasExplicitReturn continuation
  | .debug _ (some value) continuation =>
    Term.hasExplicitReturn value || Term.hasExplicitReturn continuation
termination_by term => sizeOf term
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem term.property; grind)
    | (have := List.sizeOf_lt_of_mem arg.property; grind)
    | (have := List.sizeOf_lt_of_mem arm.property
       have : sizeOf arm.val.2 < sizeOf arm.val := by cases arm.val; simp; omega
       simp_all; omega)

/-- Structurally splice `.app g args .inlined` in `t`, given `done`,
which maps each already-expanded callee to its input locals and its (already
inline-free) body. Callees containing an explicit return become normal calls
so their return cannot escape the caller. At other inline sites the inputs and body are
α-renamed to fresh `inl#N` names (`Term.freshen`, seeded with the inputs),
then each fresh input is bound to its argument via a `let`. Freshening the
inputs BEFORE binding the arguments is essential: arguments are caller terms,
so a fresh input name cannot shadow a caller local an argument references (nor
collide across copies).

Bottom-up ordering (see `Toplevel.inlineCalls`) guarantees `done[g]` is
already inline-free, so the spliced body is NOT re-traversed — the recursion
is purely structural on `t` and needs no fuel. `cnt` threads the fresh-name
counter. If `done` lacks `g` the site is left untouched; the ordering makes
that unreachable. -/
def Term.expandOnce (done : Std.HashMap Global (List Local × Term)) (cnt : Nat) :
    Term → Nat × Term := fun t => match t with
  | .app g args .inlined =>
    let (cnt, args') := args.attach.foldl (init := (cnt, ([] : List Term)))
      fun (cnt, acc) ⟨a, _⟩ => let (cnt, a') := Term.expandOnce done cnt a; (cnt, acc ++ [a'])
    match done[g]? with
    | none => (cnt, .app g args' .inlined)
    | some (ins, body) =>
      if body.hasExplicitReturn then (cnt, .app g args' .normal) else
      let (cnt, subst, freshInputs) := ins.foldl
        (init := (cnt, (∅ : Std.HashMap Local Local), ([] : List Local)))
        fun (cnt, subst, acc) inp =>
          let inp' : Local := .str s!"inl#{cnt}"
          (cnt + 1, subst.insert inp inp', acc ++ [inp'])
      let (cnt, freshBody) := Term.freshen cnt subst body
      -- A branching callee ends in a `match`. In a strict argument position
      -- the splice's leading lets hoist out (`Term.hoistLets`) but the match
      -- core would stay put, which lowering rejects as a non-tail match in
      -- arbitrary position. Bind the match to a fresh local so hoisting
      -- leaves only a variable behind; in let-RHS/tail positions the extra
      -- binding is harmless.
      let (cnt, freshBody) :=
        match Term.peelLets freshBody with
        | (fs, core@(.match ..)) =>
          let out : Local := .str s!"inl#{cnt}"
          (cnt + 1, Term.wrapLets fs (.let (.var out) core (.var out)))
        | _ => (cnt, freshBody)
      (cnt, (freshInputs.zip args').foldr
        (fun (input, arg) acc => Term.let (.var input) arg acc) freshBody)
  | .app g args mode =>
    let (cnt, args') := args.attach.foldl (init := (cnt, ([] : List Term)))
      fun (cnt, acc) ⟨a, _⟩ => let (cnt, a') := Term.expandOnce done cnt a; (cnt, acc ++ [a'])
    (cnt, .app g args' mode)
  | .unit | .var _ | .ref _ | .field _ | .u8Lit _ => (cnt, t)
  | .tuple ts =>
    let (cnt, ts') := ts.attach.foldl (init := (cnt, #[]))
      fun (cnt, acc) ⟨a, _⟩ => let (cnt, a') := Term.expandOnce done cnt a; (cnt, acc.push a')
    (cnt, .tuple ts')
  | .array ts =>
    let (cnt, ts') := ts.attach.foldl (init := (cnt, #[]))
      fun (cnt, acc) ⟨a, _⟩ => let (cnt, a') := Term.expandOnce done cnt a; (cnt, acc.push a')
    (cnt, .array ts')
  | .match s arms =>
    let (cnt, s') := Term.expandOnce done cnt s
    let (cnt, arms') := arms.attach.foldl (init := (cnt, ([] : List (Pattern × Term))))
      fun (cnt, acc) ⟨(p, a), _⟩ => let (cnt, a') := Term.expandOnce done cnt a; (cnt, acc ++ [(p, a')])
    (cnt, .match s' arms')
  | .let p v b =>
    let (cnt, v') := Term.expandOnce done cnt v
    let (cnt, b') := Term.expandOnce done cnt b
    (cnt, .let p v' b')
  | .ret a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .ret a')
  | .add a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .add a' b')
  | .sub a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .sub a' b')
  | .mul a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .mul a' b')
  | .eqZero a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .eqZero a')
  | .proj a n => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .proj a' n)
  | .get a n => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .get a' n)
  | .slice a i j => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .slice a' i j)
  | .set a n v => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, v') := Term.expandOnce done cnt v; (cnt, .set a' n v')
  | .store a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .store a')
  | .load a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .load a')
  | .ptrVal a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .ptrVal a')
  | .ann τ a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .ann τ a')
  | .assertEq a b msg c =>
    let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b
    let (cnt, c') := Term.expandOnce done cnt c; (cnt, .assertEq a' b' msg c')
  | .ioGetInfo c k => let (cnt, c') := Term.expandOnce done cnt c; let (cnt, k') := Term.expandOnce done cnt k; (cnt, .ioGetInfo c' k')
  | .ioSetInfo c k i l rv =>
    let (cnt, c') := Term.expandOnce done cnt c; let (cnt, k') := Term.expandOnce done cnt k
    let (cnt, i') := Term.expandOnce done cnt i; let (cnt, l') := Term.expandOnce done cnt l
    let (cnt, rv') := Term.expandOnce done cnt rv; (cnt, .ioSetInfo c' k' i' l' rv')
  | .ioRead c i n => let (cnt, c') := Term.expandOnce done cnt c; let (cnt, i') := Term.expandOnce done cnt i; (cnt, .ioRead c' i' n)
  | .ioWrite c d rv =>
    let (cnt, c') := Term.expandOnce done cnt c; let (cnt, d') := Term.expandOnce done cnt d
    let (cnt, rv') := Term.expandOnce done cnt rv; (cnt, .ioWrite c' d' rv')
  | .u8BitDecomposition a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .u8BitDecomposition a')
  | .u8ShiftLeft a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .u8ShiftLeft a')
  | .u8ShiftRight a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .u8ShiftRight a')
  | .u8Xor a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8Xor a' b')
  | .u8Add a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8Add a' b')
  | .u8Mul a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8Mul a' b')
  | .u8Sub a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8Sub a' b')
  | .u8And a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8And a' b')
  | .u8Or a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8Or a' b')
  | .u8LessThan a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8LessThan a' b')
  | .u32LessThan a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u32LessThan a' b')
  | .u8XorSplit7 a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8XorSplit7 a' b')
  | .u8XorSplit4 a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8XorSplit4 a' b')
  | .unconstrainedU32Add a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .unconstrainedU32Add a' b')
  | .unconstrainedU32Add3 a b c => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; let (cnt, c') := Term.expandOnce done cnt c; (cnt, .unconstrainedU32Add3 a' b' c')
  | .u32ToField a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .u32ToField a')
  | .unconstrainedBigUintDivMod a b =>
    let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .unconstrainedBigUintDivMod a' b')
  | .u8RangeCheck a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8RangeCheck a' b')
  | .toField a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .toField a')
  | .u8FromFieldUnsafe a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .u8FromFieldUnsafe a')
  | .unconstrainedGToBytes a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .unconstrainedGToBytes a')
  | .unconstrainedGInverse a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .unconstrainedGInverse a')
  | .debug s o a =>
    let (cnt, o') := match o with
      | none => (cnt, none)
      | some x => let (cnt, x') := Term.expandOnce done cnt x; (cnt, some x')
    let (cnt, a') := Term.expandOnce done cnt a
    (cnt, .debug s o' a')
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Collect leading let frames in argument order and retain their cores.
Callers must also sequence each core before later frames and avoid capture. -/
def Term.peelListLets (ts : List Term) : List (Pattern × Term) × List Term :=
  ts.foldr
    (fun t (fs, cs) => let (f, c) := Term.peelLets t; (f ++ fs, c :: cs))
    ([], [])

def Term.peelArrayLets (ts : Array Term) : List (Pattern × Term) × Array Term :=
  let (fs, cs) := Term.peelListLets ts.toList
  (fs, cs.toArray)

/-! Argument normalization uses a fresh name stem and evaluates each
argument completely before the next one. Continuations stay after their
operation; array updates evaluate the new value before the array. -/

def Pattern.maxNameLength : Pattern → Nat
  | .var (.str name) => name.length
  | .var (.idx _) | .wildcard | .field _ => 0
  | .ref global ps => ps.attach.foldl
      (fun n p => max n (Pattern.maxNameLength p.val)) global.toName.toString.length
  | .tuple ps | .array ps => ps.attach.foldl
      (fun n p => max n (Pattern.maxNameLength p.val)) 0
  | .or p q => max (Pattern.maxNameLength p) (Pattern.maxNameLength q)
  | .pointer p => Pattern.maxNameLength p
termination_by p => sizeOf p
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem p.property; grind)
    | (have := List.sizeOf_lt_of_mem p.property; grind)

def Term.maxNameLength : Term → Nat
  | .var (.str name) => name.length
  | .var (.idx _) | .unit | .field _ | .u8Lit _ => 0
  | .ref global => global.toName.toString.length
  | .app global args _ => args.attach.foldl
      (fun n arg => max n (Term.maxNameLength arg.val)) global.toName.toString.length
  | .tuple terms | .array terms => terms.attach.foldl
      (fun n term => max n (Term.maxNameLength term.val)) 0
  | .let pattern value body =>
    max (Pattern.maxNameLength pattern) (max (Term.maxNameLength value) (Term.maxNameLength body))
  | .match scrut arms => arms.attach.foldl
      (fun n arm => max n (max (Pattern.maxNameLength arm.val.1) (Term.maxNameLength arm.val.2)))
      (Term.maxNameLength scrut)
  | .ret a | .eqZero a | .proj a _ | .get a _ | .slice a _ _
  | .store a | .load a | .ptrVal a | .ann _ a
  | .u8BitDecomposition a | .u8ShiftLeft a | .u8ShiftRight a
  | .u32ToField a | .unconstrainedGToBytes a | .unconstrainedGInverse a
  | .toField a | .u8FromFieldUnsafe a => Term.maxNameLength a
  | .add a b | .sub a b | .mul a b | .set a _ b | .ioGetInfo a b | .ioRead a b _
  | .u8Xor a b | .u8Add a b | .u8Mul a b | .u8Sub a b | .u8And a b | .u8Or a b
  | .u8LessThan a b | .u32LessThan a b | .u8XorSplit7 a b | .u8XorSplit4 a b
  | .unconstrainedU32Add a b | .unconstrainedBigUintDivMod a b | .u8RangeCheck a b =>
    max (Term.maxNameLength a) (Term.maxNameLength b)
  | .assertEq a b _ c | .ioWrite a b c | .unconstrainedU32Add3 a b c =>
    max (Term.maxNameLength a) (max (Term.maxNameLength b) (Term.maxNameLength c))
  | .ioSetInfo a b c d e => max (Term.maxNameLength a)
      (max (Term.maxNameLength b) (max (Term.maxNameLength c)
        (max (Term.maxNameLength d) (Term.maxNameLength e))))
  | .debug _ none continuation => Term.maxNameLength continuation
  | .debug _ (some value) continuation => max (Term.maxNameLength value) (Term.maxNameLength continuation)
termination_by term => sizeOf term
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem term.property; grind)
    | (have := List.sizeOf_lt_of_mem arg.property; grind)
    | (have := List.sizeOf_lt_of_mem arm.property
       have : sizeOf arm.val.2 < sizeOf arm.val := by cases arm.val; simp; omega
       simp_all; omega)

def freshTemporary (stem : String) : StateM Nat Local := do
  let n ← get
  modify Nat.succ
  return .str (stem ++ toString n)

def Term.bindArguments (stem : String) :
    List Term → StateM Nat (List (Pattern × Term) × List Term)
  | [] => pure ([], [])
  | arg :: args => do
    let name ← freshTemporary stem
    let (leading, core) := arg.peelLets
    let (frames, values) ← Term.bindArguments stem args
    return (leading ++ [(.var name, core)] ++ frames, .var name :: values)

def buildWithArguments (stem : String) (args : List Term)
    (build : List Term → Term) : StateM Nat Term := do
  let (frames, values) ← Term.bindArguments stem args
  return Term.wrapLets frames (build values)

def Term.hoistLetsAux (stem : String) (term : Term) : StateM Nat Term := do
  match term with
  | .unit | .var _ | .ref _ | .field _ | .u8Lit _ => return term
  | .let pattern value body =>
    let value ← Term.hoistLetsAux stem value
    let body ← Term.hoistLetsAux stem body
    let (frames, core) := value.peelLets
    return Term.wrapLets frames (.let pattern core body)
  | .match scrut arms =>
    let scrut ← Term.hoistLetsAux stem scrut
    let arms ← arms.attach.mapM fun arm => do
      return (arm.val.1, ← Term.hoistLetsAux stem arm.val.2)
    buildWithArguments stem [scrut] fun
      | [scrut] => .match scrut arms
      | _ => term
  | .ret value =>
    let value ← Term.hoistLetsAux stem value
    let (frames, core) := value.peelLets
    return Term.wrapLets frames (.ret core)
  | .debug label value continuation =>
    let continuation ← Term.hoistLetsAux stem continuation
    return .let .wildcard (.debug label value .unit) continuation
  | .tuple terms =>
    let terms ← terms.attach.mapM fun t => Term.hoistLetsAux stem t.val
    buildWithArguments stem terms.toList (.tuple ∘ List.toArray)
  | .array terms =>
    let terms ← terms.attach.mapM fun t => Term.hoistLetsAux stem t.val
    buildWithArguments stem terms.toList (.array ∘ List.toArray)
  | .app global args mode =>
    let args ← args.attach.mapM fun t => Term.hoistLetsAux stem t.val
    buildWithArguments stem args (.app global · mode)
  | .assertEq a b msg continuation =>
    let a ← Term.hoistLetsAux stem a
    let b ← Term.hoistLetsAux stem b
    let continuation ← Term.hoistLetsAux stem continuation
    buildWithArguments stem [a, b] fun
      | [a, b] => .let .wildcard (.assertEq a b msg .unit) continuation
      | _ => term
  | .ioWrite channel data continuation =>
    let channel ← Term.hoistLetsAux stem channel
    let data ← Term.hoistLetsAux stem data
    let continuation ← Term.hoistLetsAux stem continuation
    buildWithArguments stem [channel, data] fun
      | [channel, data] => .let .wildcard (.ioWrite channel data .unit) continuation
      | _ => term
  | .ioSetInfo channel key idx len continuation =>
    let channel ← Term.hoistLetsAux stem channel
    let key ← Term.hoistLetsAux stem key
    let idx ← Term.hoistLetsAux stem idx
    let len ← Term.hoistLetsAux stem len
    let continuation ← Term.hoistLetsAux stem continuation
    buildWithArguments stem [channel, key, idx, len] fun
      | [channel, key, idx, len] => .let .wildcard (.ioSetInfo channel key idx len .unit) continuation
      | _ => term
  | .set arr index value =>
    let value ← Term.hoistLetsAux stem value
    let arr ← Term.hoistLetsAux stem arr
    buildWithArguments stem [value, arr] fun
      | [value, arr] => .set arr index value
      | _ => term
  | .add a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .add a b | _ => term
  | .sub a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .sub a b | _ => term
  | .mul a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .mul a b | _ => term
  | .ioGetInfo a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .ioGetInfo a b | _ => term
  | .ioRead a b len =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .ioRead a b len | _ => term
  | .u8Xor a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8Xor a b | _ => term
  | .u8Add a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8Add a b | _ => term
  | .u8Mul a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8Mul a b | _ => term
  | .u8Sub a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8Sub a b | _ => term
  | .u8And a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8And a b | _ => term
  | .u8Or a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8Or a b | _ => term
  | .u8LessThan a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8LessThan a b | _ => term
  | .u32LessThan a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u32LessThan a b | _ => term
  | .u8XorSplit7 a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8XorSplit7 a b | _ => term
  | .u8XorSplit4 a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8XorSplit4 a b | _ => term
  | .unconstrainedU32Add a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .unconstrainedU32Add a b | _ => term
  | .unconstrainedBigUintDivMod a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .unconstrainedBigUintDivMod a b | _ => term
  | .u8RangeCheck a b =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    buildWithArguments stem [a, b] fun | [a, b] => .u8RangeCheck a b | _ => term
  | .unconstrainedU32Add3 a b c =>
    let a ← Term.hoistLetsAux stem a; let b ← Term.hoistLetsAux stem b
    let c ← Term.hoistLetsAux stem c
    buildWithArguments stem [a, b, c] fun | [a, b, c] => .unconstrainedU32Add3 a b c | _ => term
  | .eqZero a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .eqZero a | _ => term
  | .proj a index =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .proj a index | _ => term
  | .get a index =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .get a index | _ => term
  | .slice a start stop =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .slice a start stop | _ => term
  | .store a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .store a | _ => term
  | .load a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .load a | _ => term
  | .ptrVal a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .ptrVal a | _ => term
  | .ann typ a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .ann typ a | _ => term
  | .u8BitDecomposition a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .u8BitDecomposition a | _ => term
  | .u8ShiftLeft a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .u8ShiftLeft a | _ => term
  | .u8ShiftRight a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .u8ShiftRight a | _ => term
  | .u32ToField a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .u32ToField a | _ => term
  | .unconstrainedGToBytes a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .unconstrainedGToBytes a | _ => term
  | .unconstrainedGInverse a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .unconstrainedGInverse a | _ => term
  | .toField a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .toField a | _ => term
  | .u8FromFieldUnsafe a =>
    let a ← Term.hoistLetsAux stem a
    buildWithArguments stem [a] fun | [a] => .u8FromFieldUnsafe a | _ => term
termination_by sizeOf term
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem t.property; grind)
    | (have := List.sizeOf_lt_of_mem t.property; grind)
    | (have := List.sizeOf_lt_of_mem arm.property
       have : sizeOf arm.val.2 < sizeOf arm.val := by cases arm.val; simp; omega
       simp_all; omega)

/-- Normalize argument evaluation into let bindings with distinct local
names. The name stem is longer than every original local or global name. -/
def Term.hoistLets (term : Term) : Term :=
  let stem := String.ofList (List.replicate (term.maxNameLength + 1) '#')
  let (next, renamed) := Term.freshenWith stem 0 ∅ term
  (Term.hoistLetsAux stem renamed).run' next

/-- Kahn-style topological sort of the inline-dependency graph: each pass
emits every function whose inline-callees are already emitted, so callees
precede callers. `rounds` bounds the number of passes by the function count
— a DAG on N nodes has depth < N, so N passes suffice — which is the honest
structural termination measure (not an arbitrary fuel cap). A non-empty
remaining set with no ready function is an inline cycle and is rejected. -/
def inlineTopo (deps : Std.HashMap Global (List Global)) :
    Nat → List Global → Std.HashSet Global → List Global → Except String (List Global)
  | 0, remaining, _, acc =>
    if remaining.isEmpty then pure acc
    else throw "inline recursion: dependency graph did not converge"
  | rounds + 1, remaining, emitted, acc =>
    match remaining with
    | [] => pure acc
    | _ =>
      let (ready, notReady) := remaining.partition fun g =>
        (deps.getD g []).all emitted.contains
      match ready with
      | [] =>
        throw s!"inline recursion among: {remaining.map Global.toName}"
      | _ =>
        let emitted := ready.foldl (fun s g => s.insert g) emitted
        inlineTopo deps rounds notReady emitted (acc ++ ready)
termination_by rounds _ _ _ => rounds

/-- Restore matches that `Term.expandOnce`'s non-tail wrapping
(`let out = match …; out`) placed in TAIL position back to bare tail
matches. The wrap is only needed where a splice lands in a non-tail
context; left in tail position it turns a legal tail match into a
`matchContinue` whose arms may themselves end in matches — which
lowering rejects ("non-tail match in arbitrary position"). The rewrite
is the eta step `let x = v; x → v`, applied only through tail positions
(let bodies and match arms), so non-tail wraps are untouched. -/
def Term.restoreTailMatches : Term → Term
  | .let (.var x) v (.var y) =>
    if x == y then Term.restoreTailMatches v else .let (.var x) v (.var y)
  | .let p v b => .let p v (Term.restoreTailMatches b)
  | .match s arms =>
    .match s (arms.attach.map fun arm => (arm.val.1, Term.restoreTailMatches arm.val.2))
  | t => t
termination_by term => sizeOf term
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have listBound := List.sizeOf_lt_of_mem arm.property
       have pairBound : sizeOf arm.val.2 < sizeOf arm.val := by
         cases arm.val; simp; omega
       simp_all
       omega)

/-- Inline-expand every function body in the toplevel, eliminating all
`.inlined` applications. Run before typechecking.

Bottom-up and fuel-free: `.inlined` calls form a DAG (cycles are rejected as
inline recursion), so functions are expanded in topological order — every
callee is fully expanded before any caller inlines it. Each body is therefore
expanded exactly once (`Term.expandOnce`, structurally recursive on the term),
and its already-inline-free result is memoized in `done` and spliced (with
α-renaming) at every call site. -/
def Toplevel.inlineCalls (t : Toplevel) : Except String Toplevel := do
  let funcs : Std.HashMap Global Function :=
    t.functions.foldl (fun m f => m.insert f.name f) ∅
  -- Inline dependencies per function, validating callee existence and arity.
  let deps : Std.HashMap Global (List Global) ← t.functions.foldlM (init := ∅)
    fun deps f => do
      let gs ← f.body.inlineCallSites.foldlM (init := ([] : List Global))
        fun acc (g, n) => do
          let some callee := funcs[g]?
            | throw s!"inline call to unknown function `{g.toName}`"
          if n != callee.inputs.length then
            throw s!"inline `{g.toName}`: got {n} args, expects {callee.inputs.length}"
          pure (acc ++ [g])
      pure (deps.insert f.name gs)
  -- Topological order (callees first). `funcs.size` rounds bound the passes.
  let names := t.functions.toList.map Function.name
  let order ← inlineTopo deps names.length names ∅ []
  -- Expand each body once, in order, memoizing the inline-free result.
  let done : Std.HashMap Global (List Local × Term) := order.foldl (init := ∅)
    fun done g =>
      match funcs[g]? with
      | none => done
      | some f => done.insert g (f.inputs.map Prod.fst, (f.body.expandOnce done 0).2)
  -- Rebuild each function with its expanded body, then hoist argument-position
  -- lets that splicing may have introduced.
  let functions := t.functions.map fun f =>
    match done[f.name]? with
    | none => f
    | some (_, body) => { f with body := body.restoreTailMatches.hoistLets }
  pure { t with functions }

/-- Every `Global` referenced by a term: function calls and constructor
applications via `.app`, bare references via `.ref` (constants, nullary
constructors), plus constructor names inside `let`/`match` patterns.
Non-function references never match a function name, so callers can filter
against the function table. -/
partial def Term.collectGlobals (acc : Std.HashSet Global) : Term → Std.HashSet Global
  | .unit | .var _ | .field _ | .u8Lit _ => acc
  | .ref g => acc.insert g
  | .tuple ts | .array ts => ts.foldl Term.collectGlobals acc
  | .ret t | .eqZero t | .proj t _ | .get t _ | .slice t _ _ | .store t
  | .load t | .ptrVal t | .ann _ t | .u8BitDecomposition t | .u8ShiftLeft t
  | .u8ShiftRight t | .unconstrainedGToBytes t | .unconstrainedGInverse t
  | .u32ToField t
  | .toField t | .u8FromFieldUnsafe t => t.collectGlobals acc
  | .let p v b => b.collectGlobals (v.collectGlobals (patternGlobals acc p))
  | .match s bs =>
    bs.foldl (fun a (p, b) => b.collectGlobals (patternGlobals a p))
      (s.collectGlobals acc)
  | .app g args _ => args.foldl (fun a t => t.collectGlobals a) (acc.insert g)
  | .add a b | .sub a b | .mul a b | .u8Xor a b | .u8Add a b
  | .u8Mul a b | .u8Sub a b | .u8And a b | .u8Or a b | .u8LessThan a b
  | .u32LessThan a b | .u8XorSplit7 a b | .u8XorSplit4 a b | .unconstrainedU32Add a b
  | .u8RangeCheck a b | .unconstrainedBigUintDivMod a b | .ioGetInfo a b =>
    b.collectGlobals (a.collectGlobals acc)
  | .unconstrainedU32Add3 a b c => c.collectGlobals (b.collectGlobals (a.collectGlobals acc))
  | .set a _ v => v.collectGlobals (a.collectGlobals acc)
  | .assertEq a b _ r =>
    r.collectGlobals (b.collectGlobals (a.collectGlobals acc))
  | .ioWrite a b r =>
    r.collectGlobals (b.collectGlobals (a.collectGlobals acc))
  | .ioSetInfo c k i l r =>
    r.collectGlobals (l.collectGlobals (i.collectGlobals
      (k.collectGlobals (c.collectGlobals acc))))
  | .ioRead c i _ => i.collectGlobals (c.collectGlobals acc)
  | .debug _ t r =>
    r.collectGlobals (match t with | none => acc | some t => t.collectGlobals acc)
where
  patternGlobals (acc : Std.HashSet Global) : Pattern → Std.HashSet Global
    | .var _ | .wildcard | .field _ => acc
    | .ref g ps => ps.foldl patternGlobals (acc.insert g)
    | .tuple ps | .array ps => ps.foldl patternGlobals acc
    | .or a b => patternGlobals (patternGlobals acc a) b
    | .pointer p => patternGlobals acc p

/-- Keep only the functions reachable from `roots` (entry-point names).
Data types and type aliases are kept wholesale — only functions become
circuits, so pruning functions is what shrinks the committed system (every
compiled function is a committed matrix whose openings pad every proof,
used or not). What gets dropped: `pub` entry points other than the roots
(test/bench harness entries) and any function only they reach. Relative
function order is preserved, so surviving indices stay deterministic. -/
partial def Toplevel.prune (toplevel : Toplevel) (roots : List Lean.Name) : Toplevel :=
  let byName : Std.HashMap Global Function :=
    toplevel.functions.foldl (fun a f => a.insert f.name f) ∅
  let rootGs := toplevel.functions.filterMap fun f =>
    if roots.contains f.name.toName then some f.name else none
  let rec go (todo : List Global) (seen : Std.HashSet Global) : Std.HashSet Global :=
    match todo with
    | [] => seen
    | g :: rest =>
      if seen.contains g then go rest seen
      else match byName.get? g with
        | none => go rest seen  -- constructor / datatype / alias reference
        | some f =>
          let refs := f.body.collectGlobals ∅
          go (refs.toList ++ rest) (seen.insert g)
  let keep := go rootGs.toList ∅
  { toplevel with functions := toplevel.functions.filter (keep.contains ·.name) }

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration
  deriving Repr, Inhabited

abbrev Decls := IndexMap Global Declaration

end Source

end Aiur

end -- @[expose] section
end
