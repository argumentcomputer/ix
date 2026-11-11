module

public import Lean

/-! # IxVM kernel test fixtures

Pure Lean declarations exercised by compiler and kernel test suites:
  * `IxVMPrim` — theorems whose `rfl` proofs force primitive reductions.
  * `IxVMPerf` — synthetic witnesses for delayed let inference,
    context strengthening, and multi-limb multiplication.
  * `IxVMInd` — sample inductives covering mutual blocks and nested
    parameters.
-/

/-! ## Primitive reduction theorems -/

namespace IxVMPrim

-- Nat arithmetic (try_nat_dispatch / try_nat_binop_addr)
public theorem nat_add_lit : 100 + 200 = 300 := rfl
public theorem nat_sub_lit : 1000 - 250 = 750 := rfl
public theorem nat_mul_lit : Nat.mul 6 7 = 42 := rfl
public theorem nat_mul_big : Nat.mul 1000000 1000000 = 1000000000000 := rfl
public theorem nat_div_lit : Nat.div 100 7 = 14 := rfl
public theorem nat_mod_lit : Nat.mod 100 7 = 2 := rfl
public theorem nat_succ_lit : Nat.succ 41 = 42 := rfl
public theorem nat_pred_lit : Nat.pred 42 = 41 := rfl
public theorem nat_gcd_lit : Nat.gcd 144 60 = 12 := rfl

-- Nat bitwise ops
public theorem nat_land_lit : Nat.land 0xff 0x0f = 0x0f := rfl
public theorem nat_lor_lit : Nat.lor 0xf0 0x0f = 0xff := rfl
public theorem nat_xor_lit : Nat.xor 0xff 0x0f = 0xf0 := rfl
public theorem nat_shl_lit : Nat.shiftLeft 1 8 = 256 := rfl
public theorem nat_shr_lit : Nat.shiftRight 256 4 = 16 := rfl
set_option exponentiation.threshold 65536 in
set_option maxRecDepth 65536 in
public theorem nat_pow_big : (2 ^ 16384 : Nat) - (2 ^ 16384) = 0 := rfl

-- Nat predicates (return Bool ctors)
public theorem nat_beq_lit : Nat.beq 42 42 = true := rfl
public theorem nat_ble_lit : Nat.ble 5 10 = true := rfl

public theorem nat_cases_big :
    (match (4294967296 : Nat) with | 0 => (0 : Nat) | n+1 => n) = 4294967295 := rfl

-- Decidable instances (try_reduce_decidable)
public theorem nat_dec_le : decide (5 ≤ 10) = true := rfl
public theorem nat_dec_lt : decide (5 < 10) = true := rfl
public theorem nat_dec_eq : decide (5 = 5 : Prop) = true := rfl

@[reducible] public def lazyBigOff (x : Nat) : Nat := x + 4294967295
public theorem lazy_ble_offset (x : Nat) :
    Nat.ble (lazyBigOff x) 4294967290 = Nat.ble (x + 4294967295) 4294967290 := by
  with_reducible rfl

public structure LazyUnit (scale : Nat) where
  val : Nat

public def LazyUnit.mul (x : LazyUnit a) (factor : Nat) :
    LazyUnit (a * factor) := ⟨x.val * factor⟩

public def LazyUnit.cast (_ : a = b) (x : LazyUnit a) : LazyUnit b :=
  ⟨x.val⟩

public def lazy_unit_cast (x : LazyUnit 6) : LazyUnit 60 :=
  (x.mul 10).cast (by decide +kernel)

-- String primitives (try_str_dispatch)
public theorem str_size_lit : "hello".utf8ByteSize = 5 := rfl

-- BitVec primitives (try_bitvec_dispatch)
public theorem bv_to_nat_lit : (BitVec.ofNat 16 1234).toNat = 1234 := rfl

public theorem sizeof_unit : sizeOf () = 1 := rfl

end IxVMPrim

/-! ## FLT performance regressions -/

namespace IxVMPerf

local macro "letContinuations% " n:num a:ident x:ident : term => do
  let mut body : Lean.TSyntax `term := ← `(term| $x)
  for _ in [:n.getNat] do
    body ← `(term| let saved : $a := $x
                   (fun k : $a → $a => k saved) (fun $x : $a => $body))
  return body

public def let_continuations (A : Type) (x : A) : A := letContinuations% 64 A x

local macro "mulRow% " n:num : term => do
  let mut b := 0
  let mut limb := 1
  for _ in [:n.getNat] do
    limb := (limb * 6364136223846793005 + 1442695040888963407) % 2^64
    b := b * 2^64 + limb
  let a := 2^64 - 1
  let lhs := Lean.Syntax.mkNumLit (toString a)
  let rhs := Lean.Syntax.mkNumLit (toString b)
  let product := Lean.Syntax.mkNumLit (toString (a * b))
  `(term| Nat.mul $lhs $rhs = $product)

public theorem mul_row : mulRow% 512 := rfl

local macro "contextTower% " n:num a:ident x:ident : term => do
  let mut body : Lean.TSyntax `term := ← `(term| $x)
  let mut work : Lean.TSyntax `term := ← `(term| $x)
  for _ in [:32] do
    work ← `(term| (fun z : $a => z) $work)
  for _ in [:n.getNat] do
    body ← `(term| let saved : $a := $work
                   (fun unused : Nat => $body) 0)
  return body

public def context_tower (A : Type) (x : A) : A := contextTower% 64 A x

local macro "mulWide% " n:num : term => do
  let mut a := 0
  let mut b := 0
  let mut seed := 7
  for _ in [:n.getNat] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2^64
    a := a * 2^64 + seed
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2^64
    b := b * 2^64 + seed
  let lhs := Lean.Syntax.mkNumLit (toString a)
  let rhs := Lean.Syntax.mkNumLit (toString b)
  let result := Lean.Syntax.mkNumLit (toString (a*b))
  `(term| Nat.mul $lhs $rhs = $result)

public theorem mul_wide : mulWide% 32 := rfl

end IxVMPerf

/-! ## Inductive shape fixtures -/

namespace IxVMInd

mutual
  public inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : ∀ n, Odd n → Even (n + 1)
  public inductive Odd : Nat → Prop where
    | succ : ∀ n, Even n → Odd (n + 1)
end

mutual
  public inductive IdxTeleN : Nat → Prop where
    | z : IdxTeleN 0
    | s : ∀ n, IdxTeleB true → IdxTeleN n
  public inductive IdxTeleB : Bool → Prop where
    | t : IdxTeleB true
    | f : ∀ b, IdxTeleN 0 → IdxTeleB b
end

mutual
  public inductive SoloA : Nat → Prop where
    | mk : ∀ n, SoloB true → SoloA n
  public inductive SoloB : Bool → Prop where
    | mk : ∀ b, SoloA 0 → SoloB b
end

public unsafe inductive UnsafeSquash (m : Type → Type) : Type where
  | mk : (Unit → m (UnsafeSquash m)) → UnsafeSquash m

public inductive Tree where
  | mk : List Tree → Tree

public inductive Bar2 (α β : Type) where
  | mk : α → Bar2 α β

public inductive DedupM where
  | mk : Bar2 DedupM Nat → Bar2 DedupM Bool → DedupM

public inductive PhantomBox (α : Type 2) : Type (max 2 u) where
  | mk : α → PhantomBox α

public inductive UnivM : Type 2 where
  | mk : PhantomBox.{0} UnivM → PhantomBox.{1} UnivM → UnivM

public inductive Bar1 (α : Type) where
  | mk : α → Bar1 α

public inductive DepthM (α : Type) where
  | mk : Bar1 (DepthM α) → Nat → Bar1 (DepthM α) → DepthM α

public inductive CellC (α : Type) where
  | mk : α → Char → CellC α

public inductive CellI (α : Type) where
  | mk : α → Int → CellI α

public inductive WrapC (α : Type) where
  | mk : CellC α → WrapC α

public inductive WrapI (α : Type) where
  | mk : CellI α → WrapI α

public inductive AuxTie where
  | c : WrapC AuxTie → AuxTie
  | i : WrapI AuxTie → AuxTie

public abbrev PredOver (α : Type) : Type := α → Prop

public inductive HiddenIdx (α : Type) : PredOver α where
  | mk : (a : α) → HiddenIdx α a

-- Nested blocks whose index domain mentions a parameter: the nested
-- occurrences' index arguments (`a₀`, `[]`) mention the parameters, which
-- the modeller lifts past a minor premise's binders.
public inductive NestParIdx (α : Type) (a₀ : α) : α → Type where
  | base : NestParIdx α a₀ a₀
  | mk : List (NestParIdx α a₀ a₀) → NestParIdx α a₀ a₀

public inductive NestListIdx (α : Type) : List α → Type where
  | nil : NestListIdx α []
  | mk : List (NestListIdx α []) → NestListIdx α []

-- Nested blocks with a reflexive field into a member: in a constructor of
-- the block, and in a container pinned at a function into the block (the
-- container's own field is reflexive).
public inductive NestRefl where
  | leaf : NestRefl
  | mk : (Nat → NestRefl) → List NestRefl → NestRefl

public inductive NestReflOpt where
  | leaf : NestReflOpt
  | mk : Option (Nat → NestReflOpt) → NestReflOpt

-- A field that mentions the block only where whnf erases it (`Tagged T`,
-- `Tagged _ := Nat`): Lean tests positivity after whnf, so it is ordinary.
@[expose] public def Tagged (_ : Type) : Type := Nat

public inductive Phantom where
  | leaf : Phantom
  | mk : Tagged Phantom → Phantom

public def thmMajorWant (n : Nat) (_pf : n = 1) : Nat := n

@[expose] public def thmMajorUse : Nat :=
  thmMajorWant
    (And.rec (motive := fun _ => Nat) (fun _ _ => 1)
      (⟨Nat.zero_lt_succ 0, Nat.zero_lt_succ 1⟩ : 0 < 1 ∧ 0 < 2))
    (Eq.refl 1)

public theorem partialKRec :
    (@Eq.rec Nat 0 (fun _ _ => Nat) 1 0) = (fun _ => 1) := rfl

public theorem deepRebase :
    ∀ (n : Nat) (_a _b _c _d _e _f _g _h _i _j : Nat),
      n + 0 = n :=
  fun n _ _ _ _ _ _ _ _ _ _ => Nat.add_zero n

end IxVMInd
