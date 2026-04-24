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
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  -- case .unit
  · unfold beq; rfl
  -- case .field
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
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  -- case .unit
  · intro b h
    cases b <;> (unfold beq at h; first | rfl | cases h)
  -- case .field
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
  | app : Global → List Term → (unconstrained : Bool) → Term
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
  | ioGetInfo : (key : Term) → Term
  | ioSetInfo : (key : Term) → (idx : Term) → (len : Term) → (ret : Term) → Term
  | ioRead : (idx : Term) → (len : Nat) → Term
  | ioWrite : (data : Term) → (ret : Term) → Term
  | u8BitDecomposition : Term → Term
  | u8ShiftLeft : Term → Term
  | u8ShiftRight : Term → Term
  | u8Xor : Term → Term → Term
  | u8Add : Term → Term → Term
  | u8Sub : Term → Term → Term
  | u8And : Term → Term → Term
  | u8Or : Term → Term → Term
  | u8LessThan : Term → Term → Term
  | u32LessThan : Term → Term → Term
  | debug : String → Option Term → Term → Term
  deriving Repr, BEq, Hashable, Inhabited

end Source

structure Constructor where
  nameHead : String
  argTypes : List Typ
  deriving Repr, BEq, Inhabited

instance : LawfulBEq Constructor where
  eq_of_beq := by
    intro a b h
    cases a; cases b
    rename_i n₁ a₁ n₂ a₂
    have h' : (n₁ == n₂ && a₁ == a₂) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    have e1 := eq_of_beq h1
    have e2 := eq_of_beq h2
    subst e1; subst e2; rfl
  rfl := by
    intro a
    cases a
    rename_i n a
    show (n == n && a == a) = true
    simp

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
  notPolyEntry : params = [] ∨ entry = false := by
    first | exact Or.inl rfl | exact Or.inr rfl
  deriving Repr

instance : Inhabited Function where
  default :=
    { name := default, params := [], inputs := default, output := default,
      body := default, entry := default, notPolyEntry := Or.inl rfl }

/-- Smart constructor for monomorphic functions (`params = []`). -/
def Function.mono (name : Global) (inputs : List (Local × Typ))
    (output : Typ) (body : Term) (entry : Bool) : Function :=
  { name, params := [], inputs, output, body, entry, notPolyEntry := Or.inl rfl }

/-- Smart constructor for polymorphic functions (`entry = false` forced). -/
def Function.poly (name : Global) (params : List String) (inputs : List (Local × Typ))
    (output : Typ) (body : Term) : Function :=
  { name, params, inputs, output, body, entry := false, notPolyEntry := Or.inr rfl }

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
