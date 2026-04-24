module
public import Ix.Aiur.Stages.Simple

/-!
Stage 4 (Concrete) IR — post monomorphization.

Same term shape as `Simple`, but over `Concrete.Typ` that has no `.mvar` and no
parametric `.app`. Every polymorphic decl has been specialised and renamed via
`concretizeName`. The lowering pass `toBytecode` consumes only `Concrete.Term`,
so `typSize` has no `.mvar` / `.app` arms to reject.
-/

@[expose] public section


namespace Aiur

namespace Concrete

/-- Types after monomorphization — no mvars, no parametric apps. -/
inductive Typ where
  | unit
  | field
  | tuple    : Array Typ → Typ
  | array    : Typ → Nat → Typ
  | pointer  : Typ → Typ
  /-- Monomorphic reference. The `Global` is the concretized (mangled) name. -/
  | ref      : Global → Typ
  | function : List Typ → Typ → Typ
  deriving Repr, Hashable, Inhabited

/-! ### Custom `BEq Typ` + `LawfulBEq Typ`

`deriving BEq` on nested inductives produces an opaque `beq` function that
can't be unfolded in proofs. We instead define `Typ.beq` explicitly via
well-founded recursion on `sizeOf`, then prove it decides propositional
equality. `EquivBEq Typ` and `LawfulHashable Typ` follow from the stdlib
low-priority instances `[LawfulBEq α] → EquivBEq α` and
`[LawfulBEq α] → LawfulHashable α`.
-/

namespace Typ

/-- Structural boolean equality on `Concrete.Typ`. Pairwise-compares nested
`Array Typ` and `List Typ` positions via `sizeOf` termination. -/
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
  | .function ins out, .function ins' out' =>
    beq out out' && listBeqAux ins ins'
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
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
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
  -- case .function ins out ihList ihOut
  · intro ins out ihList ihOut
    unfold beq
    simp only [Bool.and_eq_true]
    exact ⟨ihOut, ihList.1⟩
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
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
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
  | wildcard
  | field : G → Pattern
  | ref : Global → Array Local → Pattern
  | tuple : Array Local → Pattern
  | array : Array Local → Pattern
  deriving Repr, BEq, Hashable, Inhabited

/-- Plain inductive form so each sub-Term is a direct constructor child,
making `sizeOf` propagate naturally through Lean's auto-derivation.

Each constructor inlines `typ : Typ` and `escapes : Bool` as the first two
arguments. Accessors `Term.typ` and `Term.escapes` pattern-match across all
constructors. -/
inductive Term : Type where
  | unit (typ : Typ) (escapes : Bool) : Term
  | var (typ : Typ) (escapes : Bool) (l : Local) : Term
  | ref (typ : Typ) (escapes : Bool) (g : Global) : Term
  | field (typ : Typ) (escapes : Bool) (g : G) : Term
  | tuple (typ : Typ) (escapes : Bool) (ts : Array Term) : Term
  | array (typ : Typ) (escapes : Bool) (ts : Array Term) : Term
  | ret (typ : Typ) (escapes : Bool) (sub : Term) : Term
  | letVar (typ : Typ) (escapes : Bool) (l : Local) (v : Term) (b : Term) : Term
  | letWild (typ : Typ) (escapes : Bool) (v : Term) (b : Term) : Term
  /-- `letLoad typ escapes dst dstTyp src body` — see `Simple.letLoad`. -/
  | letLoad (typ : Typ) (escapes : Bool) (dst : Local) (dstTyp : Typ) (src : Local) (b : Term) : Term
  | match (typ : Typ) (escapes : Bool) (scrut : Local)
          (cases : Array (Pattern × Term)) (defaultOpt : Option Term) : Term
  | app (typ : Typ) (escapes : Bool) (g : Global) (args : List Term) (unconstrained : Bool) : Term
  | add (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | sub (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | mul (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | eqZero (typ : Typ) (escapes : Bool) (a : Term) : Term
  | proj (typ : Typ) (escapes : Bool) (a : Term) (n : Nat) : Term
  | get (typ : Typ) (escapes : Bool) (a : Term) (n : Nat) : Term
  | slice (typ : Typ) (escapes : Bool) (a : Term) (i : Nat) (j : Nat) : Term
  | set (typ : Typ) (escapes : Bool) (a : Term) (n : Nat) (v : Term) : Term
  | store (typ : Typ) (escapes : Bool) (a : Term) : Term
  | load (typ : Typ) (escapes : Bool) (a : Term) : Term
  | ptrVal (typ : Typ) (escapes : Bool) (a : Term) : Term
  | assertEq (typ : Typ) (escapes : Bool) (a : Term) (b : Term) (r : Term) : Term
  | ioGetInfo (typ : Typ) (escapes : Bool) (k : Term) : Term
  | ioSetInfo (typ : Typ) (escapes : Bool) (k i l r : Term) : Term
  | ioRead (typ : Typ) (escapes : Bool) (i : Term) (n : Nat) : Term
  | ioWrite (typ : Typ) (escapes : Bool) (d r : Term) : Term
  | u8BitDecomposition (typ : Typ) (escapes : Bool) (a : Term) : Term
  | u8ShiftLeft (typ : Typ) (escapes : Bool) (a : Term) : Term
  | u8ShiftRight (typ : Typ) (escapes : Bool) (a : Term) : Term
  | u8Xor (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8Add (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8Sub (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8And (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8Or (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u8LessThan (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | u32LessThan (typ : Typ) (escapes : Bool) (a : Term) (b : Term) : Term
  | debug (typ : Typ) (escapes : Bool) (label : String) (t : Option Term) (r : Term) : Term
  deriving Repr, Inhabited

/-- Get the type annotation of a Concrete.Term, regardless of constructor. -/
def Term.typ : Term → Typ
  | .unit t _ | .var t _ _ | .ref t _ _ | .field t _ _
  | .tuple t _ _ | .array t _ _ | .ret t _ _
  | .letVar t _ _ _ _ | .letWild t _ _ _ | .letLoad t _ _ _ _ _
  | .match t _ _ _ _ | .app t _ _ _ _
  | .add t _ _ _ | .sub t _ _ _ | .mul t _ _ _ | .eqZero t _ _
  | .proj t _ _ _ | .get t _ _ _ | .slice t _ _ _ _ | .set t _ _ _ _
  | .store t _ _ | .load t _ _ | .ptrVal t _ _
  | .assertEq t _ _ _ _ | .ioGetInfo t _ _ | .ioSetInfo t _ _ _ _ _
  | .ioRead t _ _ _ | .ioWrite t _ _ _
  | .u8BitDecomposition t _ _ | .u8ShiftLeft t _ _ | .u8ShiftRight t _ _
  | .u8Xor t _ _ _ | .u8Add t _ _ _ | .u8Sub t _ _ _
  | .u8And t _ _ _ | .u8Or t _ _ _ | .u8LessThan t _ _ _ | .u32LessThan t _ _ _
  | .debug t _ _ _ _ => t

/-- Get the escapes flag of a Concrete.Term. -/
def Term.escapes : Term → Bool
  | .unit _ e | .var _ e _ | .ref _ e _ | .field _ e _
  | .tuple _ e _ | .array _ e _ | .ret _ e _
  | .letVar _ e _ _ _ | .letWild _ e _ _ | .letLoad _ e _ _ _ _
  | .match _ e _ _ _ | .app _ e _ _ _
  | .add _ e _ _ | .sub _ e _ _ | .mul _ e _ _ | .eqZero _ e _
  | .proj _ e _ _ | .get _ e _ _ | .slice _ e _ _ _ | .set _ e _ _ _
  | .store _ e _ | .load _ e _ | .ptrVal _ e _
  | .assertEq _ e _ _ _ | .ioGetInfo _ e _ | .ioSetInfo _ e _ _ _ _
  | .ioRead _ e _ _ | .ioWrite _ e _ _
  | .u8BitDecomposition _ e _ | .u8ShiftLeft _ e _ | .u8ShiftRight _ e _
  | .u8Xor _ e _ _ | .u8Add _ e _ _ | .u8Sub _ e _ _
  | .u8And _ e _ _ | .u8Or _ e _ _ | .u8LessThan _ e _ _ | .u32LessThan _ e _ _
  | .debug _ e _ _ _ => e

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
  constructors : List Constructor
  deriving Repr, BEq, Inhabited

/-- Monomorphic function. No `params`. -/
structure Function where
  name : Global
  inputs : List (Local × Typ)
  output : Typ
  body : Term
  entry : Bool
  deriving Repr

inductive Declaration
  | function : Function → Declaration
  | dataType : DataType → Declaration
  | constructor : DataType → Constructor → Declaration
  deriving Repr, Inhabited

abbrev Decls := IndexMap Global Declaration

end Concrete

end Aiur

end -- @[expose] public section
