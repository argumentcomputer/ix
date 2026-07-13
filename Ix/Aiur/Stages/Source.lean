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
* `inlined` — the callee's body is spliced into the caller at compile
  time (no separate circuit, no interface columns). Eliminated by
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
  | assertEq : Term → Term → (ret : Term) → Term
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
  /-- Chainable right-rotation by `k` bits (1..=7) over a byte pair. -/
  | u8ChainRotr : Nat → Term → Term → Term
  /-- Unconstrained LE byte-list division-modulo hint. Inputs are two
  `List<U64>` (klimbs) values (LE limb order). Output is a tuple of two
  fresh `List<U64>` values `(q, r)` with `q*b + r = a` and `0 ≤ r < b`
  (when `b > 0`). Computed natively by the Aiur runtime via BigUint
  div_rem; no constraints generated and no per-step memo growth. The
  caller must verify `q*b + r == a` and `r < b` in constrained code. -/
  | unconstrainedBigUintDivMod : (a : Term) → (b : Term) → Term
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

/-- Rename every local bound in a pattern to a fresh `.str "inl#N"` name,
extending `subst` for the pattern's scope and advancing the fresh counter.
-/
def Pattern.freshen (cnt : Nat) (subst : Std.HashMap Local Local) :
    Pattern → Nat × Std.HashMap Local Local × Pattern
  | .var x =>
    let x' : Local := .str s!"inl#{cnt}"
    (cnt + 1, subst.insert x x', .var x')
  | .wildcard => (cnt, subst, .wildcard)
  | .field g => (cnt, subst, .field g)
  | .ref g ps =>
    let (cnt, subst, ps') := ps.attach.foldl (init := (cnt, subst, ([] : List Pattern)))
      fun (cnt, subst, acc) ⟨p, _⟩ =>
        let (cnt, subst, p') := Pattern.freshen cnt subst p
        (cnt, subst, acc ++ [p'])
    (cnt, subst, .ref g ps')
  | .tuple ps =>
    let (cnt, subst, ps') := ps.attach.foldl (init := (cnt, subst, (#[] : Array Pattern)))
      fun (cnt, subst, acc) ⟨p, _⟩ =>
        let (cnt, subst, p') := Pattern.freshen cnt subst p
        (cnt, subst, acc.push p')
    (cnt, subst, .tuple ps')
  | .array ps =>
    let (cnt, subst, ps') := ps.attach.foldl (init := (cnt, subst, (#[] : Array Pattern)))
      fun (cnt, subst, acc) ⟨p, _⟩ =>
        let (cnt, subst, p') := Pattern.freshen cnt subst p
        (cnt, subst, acc.push p')
    (cnt, subst, .array ps')
  | .or p q =>
    let (cnt, subst, p') := Pattern.freshen cnt subst p
    let (cnt, subst, q') := Pattern.freshen cnt subst q
    (cnt, subst, .or p' q')
  | .pointer p =>
    let (cnt, subst, p') := Pattern.freshen cnt subst p
    (cnt, subst, .pointer p')
termination_by p => sizeOf p
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Consistently α-rename the locals bound inside `t` to fresh names,
following `subst` for the currently-renamed variables. Used before
splicing an inlined body so its locals cannot collide with the caller's
(the `Simple` pass floats nested `let`s outward, which would otherwise
capture reused names). Only bound occurrences are rewritten; free
variables that are the callee's inputs are handled by `subst` seeded at
the call site. -/
def Term.freshen (cnt : Nat) (subst : Std.HashMap Local Local) :
    Term → Nat × Term :=
  fun t =>
  match t with
  | .var x => (cnt, .var (subst.getD x x))
  | .unit | .ref _ | .field _ | .u8Lit _ => (cnt, t)
  | .let p v b =>
    let (cnt, v') := Term.freshen cnt subst v
    let (cnt, subst', p') := Pattern.freshen cnt subst p
    let (cnt, b') := Term.freshen cnt subst' b
    (cnt, .let p' v' b')
  | .match s arms =>
    let (cnt, s') := Term.freshen cnt subst s
    let (cnt, arms') := arms.attach.foldl (init := (cnt, ([] : List (Pattern × Term))))
      fun (cnt, acc) ⟨(p, a), _⟩ =>
        let (cnt, subst', p') := Pattern.freshen cnt subst p
        let (cnt, a') := Term.freshen cnt subst' a
        (cnt, acc ++ [(p', a')])
    (cnt, .match s' arms')
  | .tuple ts =>
    let (cnt, ts') := ts.attach.foldl (init := (cnt, #[])) fun (cnt, acc) ⟨x, _⟩ =>
      let (cnt, x') := Term.freshen cnt subst x; (cnt, acc.push x')
    (cnt, .tuple ts')
  | .array ts =>
    let (cnt, ts') := ts.attach.foldl (init := (cnt, #[])) fun (cnt, acc) ⟨x, _⟩ =>
      let (cnt, x') := Term.freshen cnt subst x; (cnt, acc.push x')
    (cnt, .array ts')
  | .app g args mode =>
    let (cnt, args') := args.attach.foldl (init := (cnt, ([] : List Term))) fun (cnt, acc) ⟨x, _⟩ =>
      let (cnt, x') := Term.freshen cnt subst x; (cnt, acc ++ [x'])
    (cnt, .app g args' mode)
  | .ret a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .ret a')
  | .add a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .add a' b')
  | .sub a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .sub a' b')
  | .mul a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .mul a' b')
  | .eqZero a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .eqZero a')
  | .proj a n => let (cnt, a') := Term.freshen cnt subst a; (cnt, .proj a' n)
  | .get a n => let (cnt, a') := Term.freshen cnt subst a; (cnt, .get a' n)
  | .slice a i j => let (cnt, a') := Term.freshen cnt subst a; (cnt, .slice a' i j)
  | .set a n v => let (cnt, a') := Term.freshen cnt subst a; let (cnt, v') := Term.freshen cnt subst v; (cnt, .set a' n v')
  | .store a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .store a')
  | .load a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .load a')
  | .ptrVal a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .ptrVal a')
  | .ann τ a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .ann τ a')
  | .assertEq a b c =>
    let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; let (cnt, c') := Term.freshen cnt subst c
    (cnt, .assertEq a' b' c')
  | .ioGetInfo c k => let (cnt, c') := Term.freshen cnt subst c; let (cnt, k') := Term.freshen cnt subst k; (cnt, .ioGetInfo c' k')
  | .ioSetInfo c k i l rv =>
    let (cnt, c') := Term.freshen cnt subst c; let (cnt, k') := Term.freshen cnt subst k; let (cnt, i') := Term.freshen cnt subst i
    let (cnt, l') := Term.freshen cnt subst l; let (cnt, rv') := Term.freshen cnt subst rv
    (cnt, .ioSetInfo c' k' i' l' rv')
  | .ioRead c i n => let (cnt, c') := Term.freshen cnt subst c; let (cnt, i') := Term.freshen cnt subst i; (cnt, .ioRead c' i' n)
  | .ioWrite c d rv =>
    let (cnt, c') := Term.freshen cnt subst c; let (cnt, d') := Term.freshen cnt subst d; let (cnt, rv') := Term.freshen cnt subst rv
    (cnt, .ioWrite c' d' rv')
  | .u8BitDecomposition a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .u8BitDecomposition a')
  | .u8ShiftLeft a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .u8ShiftLeft a')
  | .u8ShiftRight a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .u8ShiftRight a')
  | .u8Xor a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8Xor a' b')
  | .u8Add a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8Add a' b')
  | .u8Mul a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8Mul a' b')
  | .u8Sub a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8Sub a' b')
  | .u8And a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8And a' b')
  | .u8Or a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8Or a' b')
  | .u8LessThan a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8LessThan a' b')
  | .u32LessThan a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u32LessThan a' b')
  | .u8ChainRotr k a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8ChainRotr k a' b')
  | .unconstrainedBigUintDivMod a b =>
    let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .unconstrainedBigUintDivMod a' b')
  | .u8RangeCheck a b => let (cnt, a') := Term.freshen cnt subst a; let (cnt, b') := Term.freshen cnt subst b; (cnt, .u8RangeCheck a' b')
  | .toField a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .toField a')
  | .u8FromFieldUnsafe a => let (cnt, a') := Term.freshen cnt subst a; (cnt, .u8FromFieldUnsafe a')
  | .debug s o a =>
    let (cnt, o') := match o with
      | none => (cnt, none)
      | some x => let (cnt, x') := Term.freshen cnt subst x; (cnt, some x')
    let (cnt, a') := Term.freshen cnt subst a
    (cnt, .debug s o' a')
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

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
  | .u8LessThan a b | .u32LessThan a b | .u8ChainRotr _ a b
  | .unconstrainedBigUintDivMod a b | .u8RangeCheck a b | .ioGetInfo a b =>
    a.inlineCallSites ++ b.inlineCallSites
  | .assertEq a b c | .ioWrite a b c => a.inlineCallSites ++ b.inlineCallSites ++ c.inlineCallSites
  | .ioSetInfo c k i l rv =>
    c.inlineCallSites ++ k.inlineCallSites ++ i.inlineCallSites ++ l.inlineCallSites ++ rv.inlineCallSites
  | .ioRead a b _ => a.inlineCallSites ++ b.inlineCallSites
  | .ret a | .eqZero a | .proj a _ | .get a _ | .slice a _ _ | .store a | .load a
  | .ptrVal a | .ann _ a | .u8BitDecomposition a | .u8ShiftLeft a | .u8ShiftRight a
  | .toField a | .u8FromFieldUnsafe a => a.inlineCallSites
  | .debug _ o a => (match o with | none => [] | some x => x.inlineCallSites) ++ a.inlineCallSites
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Structurally splice every `.app g args .inlined` in `t`, given `done`,
which maps each already-expanded callee to its input locals and its (already
inline-free) body. At an inline site the callee's inputs and body are
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
      let (cnt, subst, freshInputs) := ins.foldl
        (init := (cnt, (∅ : Std.HashMap Local Local), ([] : List Local)))
        fun (cnt, subst, acc) inp =>
          let inp' : Local := .str s!"inl#{cnt}"
          (cnt + 1, subst.insert inp inp', acc ++ [inp'])
      let (cnt, freshBody) := Term.freshen cnt subst body
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
  | .assertEq a b c =>
    let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b
    let (cnt, c') := Term.expandOnce done cnt c; (cnt, .assertEq a' b' c')
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
  | .u8ChainRotr k a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8ChainRotr k a' b')
  | .unconstrainedBigUintDivMod a b =>
    let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .unconstrainedBigUintDivMod a' b')
  | .u8RangeCheck a b => let (cnt, a') := Term.expandOnce done cnt a; let (cnt, b') := Term.expandOnce done cnt b; (cnt, .u8RangeCheck a' b')
  | .toField a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .toField a')
  | .u8FromFieldUnsafe a => let (cnt, a') := Term.expandOnce done cnt a; (cnt, .u8FromFieldUnsafe a')
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

/-- Peel the leading `let` bindings off a term: returns the binding frames
(outermost first) and the non-`let` core. -/
def Term.peelLets : Term → List (Pattern × Term) × Term
  | .let p v b => let (fs, c) := Term.peelLets b; ((p, v) :: fs, c)
  | t => ([], t)

/-- Wrap `body` in a chain of `let` frames (first frame outermost). -/
def Term.wrapLets : List (Pattern × Term) → Term → Term
  | [], body => body
  | (p, v) :: fs, body => .let p v (Term.wrapLets fs body)

/-- Peel leading lets off each of `ts` (already hoisted), collecting the
frames left-to-right so evaluation order is preserved, and returning the
frame chain plus the cores. -/
def Term.peelListLets (ts : List Term) : List (Pattern × Term) × List Term :=
  ts.foldr
    (fun t (fs, cs) => let (f, c) := Term.peelLets t; (f ++ fs, c :: cs))
    ([], [])

def Term.peelArrayLets (ts : Array Term) : List (Pattern × Term) × Array Term :=
  let (fs, cs) := Term.peelListLets ts.toList
  (fs, cs.toArray)

/-- Hoist every `let`-chain out of a strict argument position into a
wrapping `let`. Inlining splices a callee body (a `let`-chain ending in a
value) wherever the `@`-call appeared; in a `let`-RHS or tail position the
`Simple` pass already floats those lets outward, but in an argument
position (a `set`/array element, an operator operand, …) they would stay
nested, which the lowering cannot handle. This normalizes all such
positions. `let`-RHS, `match` arm bodies, and `ret`/`debug` continuations
are already handled downstream, so their lets are left in place. -/
def Term.hoistLets : Term → Term :=
  fun t =>
  -- Hoist a construct's argument terms: peel each arg's lets and wrap.
  match t with
  | .unit | .var _ | .ref _ | .field _ | .u8Lit _ => t
  | .let p v b => .let p (Term.hoistLets v) (Term.hoistLets b)
  | .match s arms =>
    let (fs, sc) := Term.peelLets (Term.hoistLets s)
    Term.wrapLets fs (.match sc (arms.attach.map fun ⟨(p, a), _⟩ => (p, Term.hoistLets a)))
  | .ret a => .ret (Term.hoistLets a)
  | .debug s o a =>
    .debug s (match o with | none => none | some x => some (Term.hoistLets x)) (Term.hoistLets a)
  | .tuple ts =>
    let (fs, cs) := Term.peelArrayLets (ts.attach.map fun ⟨x, _⟩ => Term.hoistLets x)
    Term.wrapLets fs (.tuple cs)
  | .array ts =>
    let (fs, cs) := Term.peelArrayLets (ts.attach.map fun ⟨x, _⟩ => Term.hoistLets x)
    Term.wrapLets fs (.array cs)
  | .app g args mode =>
    let (fs, cs) := Term.peelListLets (args.attach.map fun ⟨x, _⟩ => Term.hoistLets x)
    Term.wrapLets fs (.app g cs mode)
  | .assertEq a b c =>
    let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b, Term.hoistLets c]
    match cs with
    | [a, b, c] => Term.wrapLets fs (.assertEq a b c)
    | _ => t
  | .ioSetInfo a b c d e =>
    let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b, Term.hoistLets c, Term.hoistLets d, Term.hoistLets e]
    match cs with
    | [a, b, c, d, e] => Term.wrapLets fs (.ioSetInfo a b c d e)
    | _ => t
  | .ioWrite a b c =>
    let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b, Term.hoistLets c]
    match cs with
    | [a, b, c] => Term.wrapLets fs (.ioWrite a b c)
    | _ => t
  | .ioGetInfo a b =>
    let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
    match cs with | [a, b] => Term.wrapLets fs (.ioGetInfo a b) | _ => t
  | .ioRead a b n =>
    let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
    match cs with | [a, b] => Term.wrapLets fs (.ioRead a b n) | _ => t
  | .add a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                match cs with | [a, b] => Term.wrapLets fs (.add a b) | _ => t
  | .sub a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                match cs with | [a, b] => Term.wrapLets fs (.sub a b) | _ => t
  | .mul a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                match cs with | [a, b] => Term.wrapLets fs (.mul a b) | _ => t
  | .eqZero a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.eqZero c)
  | .proj a n => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.proj c n)
  | .get a n => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.get c n)
  | .slice a i j => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.slice c i j)
  | .set a n v =>
    let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets v]
    match cs with | [a, v] => Term.wrapLets fs (.set a n v) | _ => t
  | .store a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.store c)
  | .load a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.load c)
  | .ptrVal a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.ptrVal c)
  | .ann τ a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.ann τ c)
  | .u8BitDecomposition a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.u8BitDecomposition c)
  | .u8ShiftLeft a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.u8ShiftLeft c)
  | .u8ShiftRight a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.u8ShiftRight c)
  | .toField a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.toField c)
  | .u8FromFieldUnsafe a => let (fs, c) := Term.peelLets (Term.hoistLets a); Term.wrapLets fs (.u8FromFieldUnsafe c)
  | .u8Xor a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                  match cs with | [a, b] => Term.wrapLets fs (.u8Xor a b) | _ => t
  | .u8Add a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                  match cs with | [a, b] => Term.wrapLets fs (.u8Add a b) | _ => t
  | .u8Mul a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                  match cs with | [a, b] => Term.wrapLets fs (.u8Mul a b) | _ => t
  | .u8Sub a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                  match cs with | [a, b] => Term.wrapLets fs (.u8Sub a b) | _ => t
  | .u8And a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                  match cs with | [a, b] => Term.wrapLets fs (.u8And a b) | _ => t
  | .u8Or a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                 match cs with | [a, b] => Term.wrapLets fs (.u8Or a b) | _ => t
  | .u8LessThan a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                       match cs with | [a, b] => Term.wrapLets fs (.u8LessThan a b) | _ => t
  | .u32LessThan a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                        match cs with | [a, b] => Term.wrapLets fs (.u32LessThan a b) | _ => t
  | .u8ChainRotr k a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                          match cs with | [a, b] => Term.wrapLets fs (.u8ChainRotr k a b) | _ => t
  | .unconstrainedBigUintDivMod a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                                       match cs with | [a, b] => Term.wrapLets fs (.unconstrainedBigUintDivMod a b) | _ => t
  | .u8RangeCheck a b => let (fs, cs) := Term.peelListLets [Term.hoistLets a, Term.hoistLets b]
                         match cs with | [a, b] => Term.wrapLets fs (.u8RangeCheck a b) | _ => t
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

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
    | some (_, body) => { f with body := body.hoistLets }
  pure { t with functions }

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
