import IxCCGrounding.WordFire
import IxCCGrounding.WordCheck

/-!
# Hardware 64-bit Limb Primitive Adequacy (`IxCCGrounding.LimbWord`, W2)

Model-level adequacy over `Ix.Kernel.Model` for the five 64-bit hardware limb primitives of
`IxCC.BigNat.LimbOps` whose equations landed in Checkpoint 2a (`IxCC.Src.Table.limbEqnType`,
`Ix.Compile.WordEquations.limbEquations`):

1. `IxCC.BigNat.clz64 : UInt64 → UInt64`
2. `IxCC.BigNat.mulWide64 : UInt64 → UInt64 → UInt64 × UInt64`
3. `IxCC.BigNat.divWide64 : (hi lo d : UInt64) → hi < d → UInt64 × UInt64`
4. `IxCC.BigNat.addCarry64 : UInt64 → UInt64 → Bool → UInt64 × Bool`
5. `IxCC.BigNat.subBorrow64 : UInt64 → UInt64 → Bool → UInt64 × Bool`

Every equation is discharged directly over `M : Ix.Kernel.Model V env` with zero new model laws:
* `M.mem` and `M.eq_equality` (`EqBasis`) instantiate each stored limb theorem at literal / `Bool` /
  `pt` arguments;
* `M.lit_ops` (`NatAccel`) evaluates all `Nat` arithmetic (`add`, `sub`, `mul`, `div`, `mod`) and
  comparisons (`beq`, `ble`);
* `pt_mem_natLe` (`IxCCGrounding.WordLe`) supplies `divWide64`'s `hi < d` proof argument `pt`;
* `log2_accel_of_eqn` evaluates `Nat.log2` on every literal by strong induction on `Nat` from its
  single stored recurrence equation (`∀ n, Nat.log2 n = cond (Nat.ble 2 n) (Nat.succ (Nat.log2 (Nat.div n 2))) 0`);
* `ofNat_tow` (`IxCCGrounding.WordBridge`) converts every `UInt64.ofNat` input and output to its
  canonical `UInt64` word tower `towV M tk 64 (2 ^ 64) φ`;
* `proj_prod_fst` / `proj_prod_snd` (`M.proj_law`) extract the two components of each pair result,
  matching all 9 scalar `WordOp` limb components (`Lam.Erase.Limb`) and `IxCC.BigNat.LimbOps`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels Width WordOp WordResult LimbOp PrimOp)

universe w

/-! ## Keys and helper terms -/

/-- The kernel key of `Bool`. -/
abbrev boolKey : KKey := roleKey .bool

/-- The kernel term `Bool`. -/
def boolK : KExpr := .const boolKey []

/-- The kernel term of a `Bool` literal constructor. -/
def boolLitK : Bool → KExpr
  | true => .const boolTrueName []
  | false => .const boolFalseName []

/-- The 64-bit word modulus `2 ^ 64`. -/
abbrev size64 : Nat := Width.size .w64

/-- Keys beyond `TowKeys` (`w64`) named by the five `IxCC.BigNat.LimbOps` equations. -/
structure LimbKeys where
  prodTy : KKey
  prodMk : KKey
  natLog2 : KKey
  boolToNat : KKey
  cond : KKey
  deriving DecidableEq

/-- `@Prod.{0, 0} A B`. -/
def prodTyK (lk : LimbKeys) (A B : KExpr) : KExpr :=
  .app (.app (.const lk.prodTy [.zero, .zero]) A) B

/-- `@Prod.mk.{0, 0} A B a b`. -/
def prodMkK (lk : LimbKeys) (A B a b : KExpr) : KExpr :=
  Expr.mkAppN (.const lk.prodMk [.zero, .zero]) [A, B, a, b]

/-- `@cond.{0} Nat c t e`. -/
def condNatK (lk : LimbKeys) (c t e : KExpr) : KExpr :=
  Expr.mkAppN (.const lk.cond [.zero]) [natK, c, t, e]

/-- Binary `Nat` primitive application in kernel syntax. -/
def natBinK (o : PrimOp) (a b : KExpr) : KExpr :=
  .app (.app (.const (primKey o) []) a) b

/-- `UInt64.ofNat e`. -/
def of64K (tk : TowKeys) (e : KExpr) : KExpr :=
  .app (.const tk.ofNat []) e

/-! ## Stored bases for `Bool`, `Bool.toNat`, `cond`, `Nat.log2`, and `Prod` -/

/-- `Bool` and its two constructors stored as the limb equations read them. -/
structure BoolBasis (env : KEnv) : Prop where
  bool : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? boolKey = some (.indInfo cv caps) ∧ cv.levelParams = []
  bTrue : ∃ cv : ConstantVal .anon,
    env.find? boolTrueName = some (.ctorInfo cv 0 0) ∧ cv.levelParams = [] ∧ cv.type = boolK
  bFalse : ∃ cv : ConstantVal .anon,
    env.find? boolFalseName = some (.ctorInfo cv 0 0) ∧ cv.levelParams = [] ∧ cv.type = boolK

/-- `Bool.toNat` stored with its two literal evaluation equations (`false ↦ 0`, `true ↦ 1`). -/
structure BoolToNatStored (env : KEnv) (kB2N kThmF kThmT : KKey) : Prop where
  key : KeyStored env kB2N
  thmF : ∃ (cv : ConstantVal .anon) (pf : KExpr),
    env.find? kThmF = some (.thmInfo cv pf) ∧
    cv.type = eqK natK (.app (.const kB2N []) (boolLitK false)) (litE 0)
  thmT : ∃ (cv : ConstantVal .anon) (pf : KExpr),
    env.find? kThmT = some (.thmInfo cv pf) ∧
    cv.type = eqK natK (.app (.const kB2N []) (boolLitK true)) (litE 1)

/-- `cond` at `Nat` (universe 0) stored with its two branch equations (`true ↦ a`, `false ↦ b`). -/
structure CondNatStored (env : KEnv) (kCond kThmT kThmF : KKey) : Prop where
  key : ∃ ci : ConstantInfo .anon, env.find? kCond = some ci ∧ ci.toConstantVal.levelParams.length = 1
  thmT : ∃ (cv : ConstantVal .anon) (pf : KExpr) (m1 m2 : BinderMeta),
    env.find? kThmT = some (.thmInfo cv pf) ∧
    cv.type = .forallE natK (.forallE natK (eqK natK
      (Expr.mkAppN (.const kCond [.zero]) [natK, boolLitK true, .bvar 1, .bvar 0]) (.bvar 1)) m2) m1
  thmF : ∃ (cv : ConstantVal .anon) (pf : KExpr) (m1 m2 : BinderMeta),
    env.find? kThmF = some (.thmInfo cv pf) ∧
    cv.type = .forallE natK (.forallE natK (eqK natK
      (Expr.mkAppN (.const kCond [.zero]) [natK, boolLitK false, .bvar 1, .bvar 0]) (.bvar 0)) m2) m1

/-- `Nat.log2 : Nat → Nat` stored with its single recurrence equation:
`∀ n : Nat, Nat.log2 n = cond (Nat.ble 2 n) (Nat.succ (Nat.log2 (Nat.div n 2))) 0`. -/
structure Log2Stored (env : KEnv) (lk : LimbKeys) (kThm : KKey) : Prop where
  key : ∃ (ci : ConstantInfo .anon) (m : BinderMeta),
    env.find? lk.natLog2 = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type = .forallE natK natK m
  bleKey : KeyStored env (primKey .ble)
  divKey : KeyStored env (primKey .div)
  thm : ∃ (cv : ConstantVal .anon) (pf : KExpr) (m : BinderMeta),
    env.find? kThm = some (.thmInfo cv pf) ∧
    cv.type = .forallE natK (eqK natK
      (.app (.const lk.natLog2 []) (.bvar 0))
      (condNatK lk (natBinK .ble (litE 2) (.bvar 0))
        (.app (.const natSuccName []) (.app (.const lk.natLog2 []) (natBinK .div (.bvar 0) (litE 2))))
        (litE 0))) m

/-- `Prod` and `Prod.mk` stored at two level parameters, with `Prod`'s projection table for both
fields (`0` and `1`), never a proposition. -/
structure ProdBasis (env : KEnv) (lk : LimbKeys) : Prop where
  prodTy : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? lk.prodTy = some (.indInfo cv caps) ∧ cv.levelParams.length = 2
  prodMk : ∃ cv : ConstantVal .anon,
    env.find? lk.prodMk = some (.ctorInfo cv 2 2) ∧ cv.levelParams.length = 2
  proj0 : ∃ e : ProjEntry .anon, env.findProj? lk.prodTy 0 = some e ∧
    e.ctor = lk.prodMk ∧ e.numParams = 2 ∧ e.numFields = 2 ∧
    ∀ ψ, Level.eval ψ e.structSort ≠ 0
  proj1 : ∃ e : ProjEntry .anon, env.findProj? lk.prodTy 1 = some e ∧
    e.ctor = lk.prodMk ∧ e.numParams = 2 ∧ e.numFields = 2 ∧
    ∀ ψ, Level.eval ψ e.structSort ≠ 0

/-! ## Exact kernel statements of the five `IxCC.BigNat.LimbOps` equations -/

/-- Exact kernel statement of each of the five `IxCC.BigNat.LimbOps` equations
(matching `IxCC.Src.Table.limbEqnType` and `Ix.Compile.WordEquations.limbEquations`). -/
def limbStmtK (tk : TowKeys) (lk : LimbKeys) (kc : KKey) (ms : List BinderMeta) : LimbOp → KExpr
  | .clz64 =>
    let xm := natBinK .mod (.bvar 0) (litE size64)
    let isZ := natBinK .beq xm (litE 0)
    let sub63 := natBinK .sub (litE 63) (.app (.const lk.natLog2 []) xm)
    let rhs := of64K tk (condNatK lk isZ (litE 64) sub63)
    .forallE natK (eqK (.const tk.ty []) (.app (.const kc []) (of64K tk (.bvar 0))) rhs) (bmAt ms 0)
  | .mulWide64 =>
    let xm := natBinK .mod (.bvar 1) (litE size64)
    let ym := natBinK .mod (.bvar 0) (litE size64)
    let prod := natBinK .mul xm ym
    let lo := of64K tk (natBinK .mod prod (litE size64))
    let hi := of64K tk (natBinK .div prod (litE size64))
    let lhs := .app (.app (.const kc []) (of64K tk (.bvar 1))) (of64K tk (.bvar 0))
    let rhs := prodMkK lk (.const tk.ty []) (.const tk.ty []) lo hi
    .forallE natK (.forallE natK (eqK (prodTyK lk (.const tk.ty []) (.const tk.ty [])) lhs rhs)
      (bmAt ms 1)) (bmAt ms 0)
  | .divWide64 =>
    let hiM0 := natBinK .mod (.bvar 2) (litE size64)
    let dM0 := natBinK .mod (.bvar 0) (litE size64)
    let bound := leApp tk.le (.app (.const natSuccName []) hiM0) dM0
    let hiM := natBinK .mod (.bvar 3) (litE size64)
    let loM := natBinK .mod (.bvar 2) (litE size64)
    let dM := natBinK .mod (.bvar 1) (litE size64)
    let num := natBinK .add (natBinK .mul hiM (litE size64)) loM
    let q := of64K tk (natBinK .div num dM)
    let r := of64K tk (natBinK .mod num dM)
    let lhs := Expr.mkAppN (.const kc [])
      [of64K tk (.bvar 3), of64K tk (.bvar 2), of64K tk (.bvar 1), .bvar 0]
    let rhs := prodMkK lk (.const tk.ty []) (.const tk.ty []) q r
    .forallE natK (.forallE natK (.forallE natK (.forallE bound
      (eqK (prodTyK lk (.const tk.ty []) (.const tk.ty [])) lhs rhs)
      (bmAt ms 3)) (bmAt ms 2)) (bmAt ms 1)) (bmAt ms 0)
  | .addCarry64 =>
    let xm := natBinK .mod (.bvar 2) (litE size64)
    let ym := natBinK .mod (.bvar 1) (litE size64)
    let cn := .app (.const lk.boolToNat []) (.bvar 0)
    let sum := natBinK .add (natBinK .add xm ym) cn
    let carry := natBinK .ble (litE size64) sum
    let lhs := Expr.mkAppN (.const kc []) [of64K tk (.bvar 2), of64K tk (.bvar 1), .bvar 0]
    let rhs := prodMkK lk (.const tk.ty []) boolK (of64K tk sum) carry
    .forallE natK (.forallE natK (.forallE boolK
      (eqK (prodTyK lk (.const tk.ty []) boolK) lhs rhs)
      (bmAt ms 2)) (bmAt ms 1)) (bmAt ms 0)
  | .subBorrow64 =>
    let xm := natBinK .mod (.bvar 2) (litE size64)
    let ym := natBinK .mod (.bvar 1) (litE size64)
    let bn := .app (.const lk.boolToNat []) (.bvar 0)
    let sub := natBinK .add ym bn
    let borrow := natBinK .ble (.app (.const natSuccName []) xm) sub
    let hiDiff := natBinK .sub (natBinK .add (litE size64) xm) sub
    let loDiff := natBinK .sub xm sub
    let diff := condNatK lk borrow hiDiff loDiff
    let lhs := Expr.mkAppN (.const kc []) [of64K tk (.bvar 2), of64K tk (.bvar 1), .bvar 0]
    let rhs := prodMkK lk (.const tk.ty []) boolK (of64K tk diff) borrow
    .forallE natK (.forallE natK (.forallE boolK
      (eqK (prodTyK lk (.const tk.ty []) boolK) lhs rhs)
      (bmAt ms 2)) (bmAt ms 1)) (bmAt ms 0)

/-- The `Nat` primitive operations referenced by a `LimbOp`'s stored equation. -/
def limbPrimOps : LimbOp → List PrimOp
  | .clz64 => [.mod, .beq, .sub]
  | .mulWide64 => [.mod, .mul, .div]
  | .divWide64 => [.mod, .mul, .add, .div]
  | .addCarry64 => [.mod, .add, .ble]
  | .subBorrow64 => [.mod, .add, .ble, .sub]

/-- Stored theorem check for a single `LimbOp`. -/
def LimbStmt (env : KEnv) (tk : TowKeys) (lk : LimbKeys) (kc kThm : KKey) (op : LimbOp) : Prop :=
  KeyStored env kc ∧
  KeyStored env tk.ty ∧
  (∀ o ∈ limbPrimOps op, KeyStored env (primKey o)) ∧
  ∃ (cv : ConstantVal .anon) (pf : KExpr) (ms : List BinderMeta),
    env.find? kThm = some (.thmInfo cv pf) ∧ cv.type = limbStmtK tk lk kc ms op

/-! ## Model-level semantics and evaluation lemmas -/

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- Denotation of a `Bool` literal in `M`. -/
noncomputable def boolSet (M : Model V env) (φ : LevelParam → Nat) (b : Bool) : V :=
  M.cval (if b then boolTrueName else boolFalseName) φ

/-- Denotation of `@Prod.mk.{0, 0} A B a b` in `M`, given `Prod.mk`'s two level parameter names. -/
noncomputable def prodV (M : Model V env) (kMk : KKey) (lpsP : List LevelParam)
    (φ : LevelParam → Nat) (A B a b : V) : V :=
  [A, B, a, b].foldl app (M.cval kMk (Level.substFn φ lpsP [.zero, .zero]))

theorem bool_den (M : Model V env) (hB : BoolBasis env) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ boolK (M.cval boolKey φ) := by
  obtain ⟨cv, caps, hf, hl⟩ := hB.bool
  exact (den_const0 (ci := .indInfo cv caps) hf hl).mpr rfl

theorem boolLit_den (M : Model V env) (hB : BoolBasis env) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (b : Bool) : Denotes M.cval env φ ρ (boolLitK b) (boolSet M φ b) := by
  cases b with
  | true =>
    obtain ⟨cv, hf, hl, -⟩ := hB.bTrue
    exact (den_const0 hf hl).mpr rfl
  | false =>
    obtain ⟨cv, hf, hl, -⟩ := hB.bFalse
    exact (den_const0 hf hl).mpr rfl

theorem boolLit_mem (M : Model V env) (hB : BoolBasis env) (φ : LevelParam → Nat) (b : Bool) :
    boolSet M φ b ∈ˢ M.cval boolKey φ := by
  cases b with
  | true =>
    obtain ⟨cv, hf, -, ht⟩ := hB.bTrue
    obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, ht] at hT
    rwa [Denotes_functional hT (bool_den M hB φ _)] at hm
  | false =>
    obtain ⟨cv, hf, -, ht⟩ := hB.bFalse
    obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, ht] at hT
    rwa [Denotes_functional hT (bool_den M hB φ _)] at hm

/-- Evaluate a `Nat` comparison primitive (`Nat.beq`, `Nat.ble`) on literals in `M`. -/
theorem natCmp_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hB : BoolBasis env)
    {op : PrimOp} (hop : op = .beq ∨ op = .ble) (hk : KeyStored env (primKey op))
    (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b) =
      boolSet M φ (match op with | .beq => a == b | .ble => decide (a ≤ b) | _ => false) := by
  have hF := natFacts M hN φ
  let ρ0 : BVarIdx → V := fun _ => empty
  have har : op.arity ≠ 1 := by rcases hop with rfl | rfl <;> decide
  have hprim : Denotes M.cval env φ ρ0 (primApp op a b)
      (app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b)) := by
    simp only [primApp, har, ↓reduceIte]
    exact .app (.app (hk.den M φ ρ0) ((lit_den M hF ρ0 a _).mpr rfl))
      ((lit_den M hF ρ0 b _).mpr rfl)
  have hres := hacc op a b φ ρ0 _ (fun h => absurd h har) hprim
  rcases hop with rfl | rfl
  · simp only [PrimOp.eval2, primResultE] at hres
    cases h : (a == b) <;> rw [h] at hres
    · exact Denotes_functional hres (boolLit_den M hB φ ρ0 false)
    · exact Denotes_functional hres (boolLit_den M hB φ ρ0 true)
  · simp only [PrimOp.eval2, primResultE] at hres
    cases h : decide (a ≤ b) <;> rw [h] at hres
    · exact Denotes_functional hres (boolLit_den M hB φ ρ0 false)
    · exact Denotes_functional hres (boolLit_den M hB φ ρ0 true)

/-- Evaluate a binary `Nat` arithmetic primitive on literals in `M`. -/
theorem natArith_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {op : PrimOp} (ha : NForm.arith op = true) (hk : KeyStored env (primKey op))
    (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b) =
      litSet M φ (NForm.natOp op a b) := by
  have hF := natFacts M hN φ
  let ρ0 : BVarIdx → V := fun _ => empty
  have hfd := form_den M hacc hN (ρ := ρ0) (ex := litE a) (ey := litE b) (vx := a) (vy := b)
    ((lit_den M hF ρ0 a _).mpr rfl) ((lit_den M hF ρ0 b _).mpr rfl) (.op op .x .y)
    (by simp [NForm.ok, ha])
    (fun o ho => by simp [NForm.ops] at ho; subst ho; exact hk)
  have hd : Denotes M.cval env φ ρ0 ((NForm.op op .x .y).toK (litE a) (litE b))
      (app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b)) :=
    .app (.app (hk.den M φ ρ0) ((lit_den M hF ρ0 a _).mpr rfl)) ((lit_den M hF ρ0 b _).mpr rfl)
  exact Denotes_functional hd hfd

theorem natAdd_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hk : KeyStored env (primKey .add)) (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey .add) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ (a + b) :=
  natArith_accel M hacc hN (op := .add) rfl hk φ a b

theorem natSub_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hk : KeyStored env (primKey .sub)) (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey .sub) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ (a - b) :=
  natArith_accel M hacc hN (op := .sub) rfl hk φ a b

theorem natMul_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hk : KeyStored env (primKey .mul)) (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey .mul) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ (a * b) :=
  natArith_accel M hacc hN (op := .mul) rfl hk φ a b

theorem natDiv_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hk : KeyStored env (primKey .div)) (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey .div) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ (a / b) :=
  natArith_accel M hacc hN (op := .div) rfl hk φ a b

theorem natMod_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hk : KeyStored env (primKey .mod)) (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval (primKey .mod) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ (a % b) :=
  natArith_accel M hacc hN (op := .mod) rfl hk φ a b

/-- `Bool.toNat` on `false`/`true` in `M` from its two stored equations. -/
theorem boolToNat_accel (M : Model V env) (hN : NatBasis env) (hB : BoolBasis env)
    (hE : EqBasis env) {kB2N kThmF kThmT : KKey} (hBN : BoolToNatStored env kB2N kThmF kThmT)
    (φ : LevelParam → Nat) (b : Bool) :
    app (M.cval kB2N φ) (boolSet M φ b) = litSet M φ b.toNat := by
  have hF := natFacts M hN φ
  let ρ0 : BVarIdx → V := fun _ => empty
  cases b with
  | false =>
    obtain ⟨cv, pf, hf, ht⟩ := hBN.thmF
    obtain ⟨T, hT, hm⟩ := mem_key M hf φ ρ0
    simp only [ConstantInfo.toConstantVal, ht, eqK] at hT
    obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hT hm
    have hlhs : Denotes M.cval env φ ρ0 (.app (.const kB2N []) (boolLitK false))
        (app (M.cval kB2N φ) (boolSet M φ false)) :=
      .app (hBN.key.den M φ ρ0) (boolLit_den M hB φ ρ0 false)
    exact (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 ((lit_den M hF ρ0 0 _).mpr rfl))
  | true =>
    obtain ⟨cv, pf, hf, ht⟩ := hBN.thmT
    obtain ⟨T, hT, hm⟩ := mem_key M hf φ ρ0
    simp only [ConstantInfo.toConstantVal, ht, eqK] at hT
    obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hT hm
    have hlhs : Denotes M.cval env φ ρ0 (.app (.const kB2N []) (boolLitK true))
        (app (M.cval kB2N φ) (boolSet M φ true)) :=
      .app (hBN.key.den M φ ρ0) (boolLit_den M hB φ ρ0 true)
    exact (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 ((lit_den M hF ρ0 1 _).mpr rfl))

/-- `@cond.{0} Nat` on `true`/`false` and any two members of `⟦Nat⟧` in `M`. -/
theorem condNat_accel (M : Model V env) (hN : NatBasis env) (hB : BoolBasis env) (hE : EqBasis env)
    {kCond kThmT kThmF : KKey} (hC : CondNatStored env kCond kThmT kThmF)
    {ciC : ConstantInfo .anon} (hfC : env.find? kCond = some ciC)
    (φ : LevelParam → Nat) (b : Bool) {x y : V}
    (hx : x ∈ˢ M.cval natName φ) (hy : y ∈ˢ M.cval natName φ) :
    [M.cval natName φ, boolSet M φ b, x, y].foldl app
      (M.cval kCond (Level.substFn φ ciC.toConstantVal.levelParams [.zero])) =
      if b then x else y := by
  have hF := natFacts M hN φ
  obtain ⟨ciC', hfC', hlC'⟩ := hC.key
  rw [hfC] at hfC'
  cases hfC'
  let ρ0 : BVarIdx → V := fun _ => empty
  let ρ2 : BVarIdx → V := push y (push x ρ0)
  have hK : Denotes M.cval env φ ρ2 (.const kCond [.zero])
      (M.cval kCond (Level.substFn φ ciC.toConstantVal.levelParams [.zero])) :=
    Denotes.const hfC (by simp [hlC'])
  cases b with
  | true =>
    obtain ⟨cv, pf, m1, m2, hf, ht⟩ := hC.thmT
    obtain ⟨TT, hTT, hm⟩ := mem_key M hf φ ρ0
    simp only [ConstantInfo.toConstantVal, ht, eqK] at hTT
    obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm hx
    obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 hy
    obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hB2 hm2
    have hlhs : Denotes M.cval env φ ρ2
        (Expr.mkAppN (.const kCond [.zero]) [natK, boolLitK true, .bvar 1, .bvar 0])
        ([M.cval natName φ, boolSet M φ true, x, y].foldl app
          (M.cval kCond (Level.substFn φ ciC.toConstantVal.levelParams [.zero]))) := by
      simp only [Expr.mkAppN, List.foldl_cons, List.foldl_nil]
      exact .app (.app (.app (.app hK ((hF.natD _ _).mpr rfl)) (boolLit_den M hB φ ρ2 true))
        (.bvar (i := 1))) (.bvar (i := 0))
    have hrhs : Denotes M.cval env φ ρ2 (.bvar 1) x := .bvar (i := 1)
    simpa using (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
  | false =>
    obtain ⟨cv, pf, m1, m2, hf, ht⟩ := hC.thmF
    obtain ⟨TT, hTT, hm⟩ := mem_key M hf φ ρ0
    simp only [ConstantInfo.toConstantVal, ht, eqK] at hTT
    obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm hx
    obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 hy
    obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hB2 hm2
    have hlhs : Denotes M.cval env φ ρ2
        (Expr.mkAppN (.const kCond [.zero]) [natK, boolLitK false, .bvar 1, .bvar 0])
        ([M.cval natName φ, boolSet M φ false, x, y].foldl app
          (M.cval kCond (Level.substFn φ ciC.toConstantVal.levelParams [.zero]))) := by
      simp only [Expr.mkAppN, List.foldl_cons, List.foldl_nil]
      exact .app (.app (.app (.app hK ((hF.natD _ _).mpr rfl)) (boolLit_den M hB φ ρ2 false))
        (.bvar (i := 1))) (.bvar (i := 0))
    have hrhs : Denotes M.cval env φ ρ2 (.bvar 0) y := .bvar (i := 0)
    simpa using (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)

/-- `Nat.log2` on any member of `⟦Nat⟧` stays in `⟦Nat⟧` (`M.mem`). -/
theorem log2_mem (M : Model V env) (hN : NatBasis env) {lk : LimbKeys} {kThm : KKey}
    (hLog : Log2Stored env lk kThm) (φ : LevelParam → Nat) {x : V}
    (hx : x ∈ˢ M.cval natName φ) : app (M.cval lk.natLog2 φ) x ∈ˢ M.cval natName φ := by
  have hF := natFacts M hN φ
  obtain ⟨ci, m, hf, -, ht⟩ := hLog.key
  obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
  rw [ht] at hT
  obtain ⟨B, hB, happ⟩ := app_mem_den_pi hT ((hF.natD _ _).mpr rfl) hm hx
  rwa [(hF.natD _ B).mp hB] at happ

/-- **`Nat.log2` on literals in every `Ix.Kernel.Model`**, by strong induction on `n : Nat`
from its single stored recurrence theorem (zero new model laws). -/
theorem log2_accel_of_eqn (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) {lk : LimbKeys} {kCT kCF kLogThm : KKey}
    (hC : CondNatStored env lk.cond kCT kCF) (hLog : Log2Stored env lk kLogThm)
    (φ : LevelParam → Nat) :
    ∀ n : Nat, app (M.cval lk.natLog2 φ) (litSet M φ n) = litSet M φ (Nat.log2 n) := by
  have hF := natFacts M hN φ
  obtain ⟨ciL, -, hfL, hlL, -⟩ := hLog.key
  obtain ⟨ciC, hfC, hlC⟩ := hC.key
  obtain ⟨cvT, pfT, mT, hfT, htT⟩ := hLog.thm
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    let ρ0 : BVarIdx → V := fun _ => empty
    let ρ1 : BVarIdx → V := push (litSet M φ n) ρ0
    obtain ⟨v, hv1, hv2⟩ := thm_inst1 M hN hE hfT (by simpa [eqK] using htT) φ n
    have hlhs : Denotes M.cval env φ ρ1 (.app (.const lk.natLog2 []) (.bvar 0))
        (app (M.cval lk.natLog2 φ) (litSet M φ n)) :=
      .app ((den_const0 hfL hlL).mpr rfl) .bvar
    have hbleD : Denotes M.cval env φ ρ1 (natBinK .ble (litE 2) (.bvar 0))
        (boolSet M φ (decide (2 ≤ n))) := by
      rw [← natCmp_accel M hacc hN hB (.inr rfl) hLog.bleKey φ 2 n]
      exact .app (.app (hLog.bleKey.den M φ ρ1) ((lit_den M hF ρ1 2 _).mpr rfl)) .bvar
    have hdivD : Denotes M.cval env φ ρ1 (natBinK .div (.bvar 0) (litE 2))
        (litSet M φ (n / 2)) := by
      rw [← natDiv_accel M hacc hN hLog.divKey φ n 2]
      exact .app (.app (hLog.divKey.den M φ ρ1) .bvar) ((lit_den M hF ρ1 2 _).mpr rfl)
    let branchT : V := app (M.cval natSuccName φ) (app (M.cval lk.natLog2 φ) (litSet M φ (n / 2)))
    have hbrTD : Denotes M.cval env φ ρ1
        (.app (.const natSuccName []) (.app (.const lk.natLog2 []) (natBinK .div (.bvar 0) (litE 2))))
        branchT :=
      .app ((hF.succD _ _).mpr rfl) (.app ((den_const0 hfL hlL).mpr rfl) hdivD)
    have hK : Denotes M.cval env φ ρ1 (.const lk.cond [.zero])
        (M.cval lk.cond (Level.substFn φ ciC.toConstantVal.levelParams [.zero])) :=
      Denotes.const hfC (by simp [hlC])
    have hrhs : Denotes M.cval env φ ρ1
        (condNatK lk (natBinK .ble (litE 2) (.bvar 0))
          (.app (.const natSuccName []) (.app (.const lk.natLog2 []) (natBinK .div (.bvar 0) (litE 2))))
          (litE 0))
        ([M.cval natName φ, boolSet M φ (decide (2 ≤ n)), branchT, litSet M φ 0].foldl app
          (M.cval lk.cond (Level.substFn φ ciC.toConstantVal.levelParams [.zero]))) := by
      simp only [condNatK, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
      exact .app (.app (.app (.app hK ((hF.natD _ _).mpr rfl)) hbleD) hbrTD)
        ((lit_den M hF ρ1 0 _).mpr rfl)
    have heq := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
    have hbrTMem : branchT ∈ˢ M.cval natName φ :=
      hF.succMem _ (log2_mem M hN hLog φ (lit_mem M hF (n / 2)))
    have hcondEq := condNat_accel M hN hB hE hC hfC φ (decide (2 ≤ n)) hbrTMem (lit_mem M hF 0)
    rw [hcondEq] at heq
    rw [heq]
    by_cases h2 : 2 ≤ n
    · have hlt : n / 2 < n := by omega
      have hlog : Nat.log2 n = Nat.log2 (n / 2) + 1 := by rw [Nat.log2_def]; simp [h2]
      simp only [h2, decide_true, ↓reduceIte, branchT, ih (n / 2) hlt, hlog]
      rfl
    · have hlog : Nat.log2 n = 0 := by rw [Nat.log2_def]; simp [h2]
      simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, hlog]

/-! ## The five `IxCC.BigNat.LimbOps` model acceleration theorems -/

/-- **1. `clz64` adequacy over `Ix.Kernel.Model`**: for every `x < 2 ^ 64`, `clz64` applied to
`x`'s canonical `UInt64` tower equals the tower of `if x == 0 then 64 else 63 - Nat.log2 x`. -/
theorem clz64_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hB : BoolBasis env)
    (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys} {kB kR kS kCT kCF kLogThm kc kThm : KKey}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hC : CondNatStored env lk.cond kCT kCF) (hLog : Log2Stored env lk kLogThm)
    (hst : LimbStmt env tk lk kc kThm .clz64) (φ : LevelParam → Nat) {x : Nat} (hx : x < size64) :
    app (M.cval kc φ) (towV M tk 64 size64 φ x) =
      towV M tk 64 size64 φ (if x == 0 then 64 else 63 - Nat.log2 x) := by
  have hF := natFacts M hN φ
  obtain ⟨hkc, -, hops, cvT, pfT, ms, hfT, htT⟩ := hst
  obtain ⟨ciL, -, hfL, hlL, -⟩ := hLog.key
  obtain ⟨ciC, hfC, hlC⟩ := hC.key
  have hofN : ∀ a, app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk 64 size64 φ (a % size64) :=
    ofNat_tow M hacc hN hE hBr φ
  have hofD : ∀ ρ, Denotes M.cval env φ ρ (.const tk.ofNat []) (M.cval tk.ofNat φ) :=
    hBr.den M (by simp) φ
  have hxt : app (M.cval tk.ofNat φ) (litSet M φ x) = towV M tk 64 size64 φ x := by
    rw [hofN x, Nat.mod_eq_of_lt hx]
  rw [← hxt]
  let ρ1 : BVarIdx → V := push (litSet M φ x) (fun _ => empty)
  obtain ⟨v, hv1, hv2⟩ := thm_inst1 M hN hE hfT (by simpa [limbStmtK, eqK] using htT) φ x
  have hlhs : Denotes M.cval env φ ρ1 (.app (.const kc []) (of64K tk (.bvar 0)))
      (app (M.cval kc φ) (app (M.cval tk.ofNat φ) (litSet M φ x))) :=
    .app (hkc.den M φ ρ1) (.app (hofD ρ1) .bvar)
  have hmodD : Denotes M.cval env φ ρ1 (natBinK .mod (.bvar 0) (litE size64)) (litSet M φ x) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ1) (i := 0) (a := x) .bvar
    rwa [Nat.mod_eq_of_lt hx] at h
  have hbeqK : KeyStored env (primKey .beq) := hops .beq (by simp [limbPrimOps])
  have hsubK : KeyStored env (primKey .sub) := hops .sub (by simp [limbPrimOps])
  have hisZD : Denotes M.cval env φ ρ1
      (natBinK .beq (natBinK .mod (.bvar 0) (litE size64)) (litE 0))
      (boolSet M φ (x == 0)) := by
    rw [← natCmp_accel M hacc hN hB (.inl rfl) hbeqK φ x 0]
    exact .app (.app (hbeqK.den M φ ρ1) hmodD) ((lit_den M hF ρ1 0 _).mpr rfl)
  have hlogD : Denotes M.cval env φ ρ1
      (.app (.const lk.natLog2 []) (natBinK .mod (.bvar 0) (litE size64)))
      (litSet M φ (Nat.log2 x)) := by
    rw [← log2_accel_of_eqn M hacc hN hB hE hC hLog φ x]
    exact .app ((den_const0 hfL hlL).mpr rfl) hmodD
  have hsubD : Denotes M.cval env φ ρ1
      (natBinK .sub (litE 63) (.app (.const lk.natLog2 []) (natBinK .mod (.bvar 0) (litE size64))))
      (litSet M φ (63 - Nat.log2 x)) := by
    rw [← natSub_accel M hacc hN hsubK φ 63 (Nat.log2 x)]
    exact .app (.app (hsubK.den M φ ρ1) ((lit_den M hF ρ1 63 _).mpr rfl)) hlogD
  have hcondK : Denotes M.cval env φ ρ1 (.const lk.cond [.zero])
      (M.cval lk.cond (Level.substFn φ ciC.toConstantVal.levelParams [.zero])) :=
    Denotes.const hfC (by simp [hlC])
  have hcondVal := condNat_accel M hN hB hE hC hfC φ (x == 0)
    (lit_mem M hF 64) (lit_mem M hF (63 - Nat.log2 x))
  have hcondD : Denotes M.cval env φ ρ1
      (condNatK lk (natBinK .beq (natBinK .mod (.bvar 0) (litE size64)) (litE 0))
        (litE 64) (natBinK .sub (litE 63) (.app (.const lk.natLog2 []) (natBinK .mod (.bvar 0) (litE size64)))))
      (litSet M φ (if x == 0 then 64 else 63 - Nat.log2 x)) := by
    have h0 : Denotes M.cval env φ ρ1
        (condNatK lk (natBinK .beq (natBinK .mod (.bvar 0) (litE size64)) (litE 0))
          (litE 64) (natBinK .sub (litE 63) (.app (.const lk.natLog2 []) (natBinK .mod (.bvar 0) (litE size64)))))
        ([M.cval natName φ, boolSet M φ (x == 0), litSet M φ 64, litSet M φ (63 - Nat.log2 x)].foldl app
          (M.cval lk.cond (Level.substFn φ ciC.toConstantVal.levelParams [.zero]))) := by
      simp only [condNatK, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
      exact .app (.app (.app (.app hcondK ((hF.natD _ _).mpr rfl)) hisZD)
        ((lit_den M hF ρ1 64 _).mpr rfl)) hsubD
    rw [hcondVal] at h0
    split <;> simpa [*] using h0
  have hrhs : Denotes M.cval env φ ρ1
      (of64K tk (condNatK lk (natBinK .beq (natBinK .mod (.bvar 0) (litE size64)) (litE 0))
        (litE 64) (natBinK .sub (litE 63) (.app (.const lk.natLog2 []) (natBinK .mod (.bvar 0) (litE size64))))))
      (app (M.cval tk.ofNat φ) (litSet M φ (if x == 0 then 64 else 63 - Nat.log2 x))) :=
    .app (hofD ρ1) hcondD
  have heq := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
  rw [heq, hofN]
  have hlt : (if x == 0 then 64 else 63 - Nat.log2 x) < size64 := by
    split <;> (simp only [size64, Width.size, Width.bits]; omega)
  rw [Nat.mod_eq_of_lt hlt]

/-- **`clz64` matches `IxCC.BigNat.clz64` directly in every `Ix.Kernel.Model`.** -/
theorem clz64_accel_bignat (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys}
    {kB kR kS kCT kCF kLogThm kc kThm : KKey}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hC : CondNatStored env lk.cond kCT kCF) (hLog : Log2Stored env lk kLogThm)
    (hst : LimbStmt env tk lk kc kThm .clz64) (φ : LevelParam → Nat) (x : UInt64) :
    app (M.cval kc φ) (towV M tk 64 size64 φ x.toNat) =
      towV M tk 64 size64 φ (IxCC.BigNat.clz64 x).toNat := by
  rw [clz64_accel M hacc hN hB hE hBr hC hLog hst φ (IxCC.BigNat.uint64_toNat_lt x)]
  have hc := LimbOp.clz64_conservative x
  simpa [WordOp.eval, WordResult.val] using congrArg (towV M tk 64 size64 φ) hc

/-- **2. `mulWide64` adequacy over `Ix.Kernel.Model`**: for all `x y < 2 ^ 64`, `mulWide64` applied
to `x` and `y`'s towers equals `Prod.mk UInt64 UInt64 (towV ((x * y) % 2^64)) (towV ((x * y) / 2^64))`. -/
theorem mulWide64_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hE : EqBasis env)
    {tk : TowKeys} {lk : LimbKeys} {kB kR kS kc kThm : KKey} {cvP : ConstantVal .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .mulWide64) (φ : LevelParam → Nat)
    {x y : Nat} (hx : x < size64) (hy : y < size64) :
    app (app (M.cval kc φ) (towV M tk 64 size64 φ x)) (towV M tk 64 size64 φ y) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval tk.ty φ)
        (towV M tk 64 size64 φ ((x * y) % size64))
        (towV M tk 64 size64 φ ((x * y) / size64)) := by
  have hF := natFacts M hN φ
  obtain ⟨hkc, hty, hops, cvT, pfT, ms, hfT, htT⟩ := hst
  have hofN : ∀ a, app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk 64 size64 φ (a % size64) :=
    ofNat_tow M hacc hN hE hBr φ
  have hofD : ∀ ρ, Denotes M.cval env φ ρ (.const tk.ofNat []) (M.cval tk.ofNat φ) :=
    hBr.den M (by simp) φ
  have hxT : app (M.cval tk.ofNat φ) (litSet M φ x) = towV M tk 64 size64 φ x := by
    rw [hofN x, Nat.mod_eq_of_lt hx]
  have hyT : app (M.cval tk.ofNat φ) (litSet M φ y) = towV M tk 64 size64 φ y := by
    rw [hofN y, Nat.mod_eq_of_lt hy]
  rw [← hxT, ← hyT]
  let ρ2 : BVarIdx → V := push (litSet M φ y) (push (litSet M φ x) (fun _ => empty))
  obtain ⟨v, hv1, hv2⟩ := thm_inst2 M hN hE hfT (by simpa [limbStmtK, eqK] using htT) φ x y
  have hlhs : Denotes M.cval env φ ρ2
      (.app (.app (.const kc []) (of64K tk (.bvar 1))) (of64K tk (.bvar 0)))
      (app (app (M.cval kc φ) (app (M.cval tk.ofNat φ) (litSet M φ x)))
        (app (M.cval tk.ofNat φ) (litSet M φ y))) :=
    .app (.app (hkc.den M φ ρ2) (.app (hofD ρ2) (.bvar (i := 1)))) (.app (hofD ρ2) (.bvar (i := 0)))
  have hmodX : Denotes M.cval env φ ρ2 (natBinK .mod (.bvar 1) (litE size64)) (litSet M φ x) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ2) (i := 1) (a := x) (.bvar (i := 1))
    rwa [Nat.mod_eq_of_lt hx] at h
  have hmodY : Denotes M.cval env φ ρ2 (natBinK .mod (.bvar 0) (litE size64)) (litSet M φ y) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ2) (i := 0) (a := y) (.bvar (i := 0))
    rwa [Nat.mod_eq_of_lt hy] at h
  have hmulK : KeyStored env (primKey .mul) := hops .mul (by simp [limbPrimOps])
  have hmodK : KeyStored env (primKey .mod) := hops .mod (by simp [limbPrimOps])
  have hdivK : KeyStored env (primKey .div) := hops .div (by simp [limbPrimOps])
  have hprodD : Denotes M.cval env φ ρ2
      (natBinK .mul (natBinK .mod (.bvar 1) (litE size64)) (natBinK .mod (.bvar 0) (litE size64)))
      (litSet M φ (x * y)) := by
    rw [← natMul_accel M hacc hN hmulK φ x y]
    exact .app (.app (hmulK.den M φ ρ2) hmodX) hmodY
  have hloD : Denotes M.cval env φ ρ2
      (of64K tk (natBinK .mod (natBinK .mul (natBinK .mod (.bvar 1) (litE size64))
        (natBinK .mod (.bvar 0) (litE size64))) (litE size64)))
      (app (M.cval tk.ofNat φ) (litSet M φ ((x * y) % size64))) := by
    refine .app (hofD ρ2) ?_
    rw [← natMod_accel M hacc hN hmodK φ (x * y) size64]
    exact .app (.app (hmodK.den M φ ρ2) hprodD) ((lit_den M hF ρ2 size64 _).mpr rfl)
  have hhiD : Denotes M.cval env φ ρ2
      (of64K tk (natBinK .div (natBinK .mul (natBinK .mod (.bvar 1) (litE size64))
        (natBinK .mod (.bvar 0) (litE size64))) (litE size64)))
      (app (M.cval tk.ofNat φ) (litSet M φ ((x * y) / size64))) := by
    refine .app (hofD ρ2) ?_
    rw [← natDiv_accel M hacc hN hdivK φ (x * y) size64]
    exact .app (.app (hdivK.den M φ ρ2) hprodD) ((lit_den M hF ρ2 size64 _).mpr rfl)
  have hmkD : Denotes M.cval env φ ρ2 (.const lk.prodMk [.zero, .zero])
      (M.cval lk.prodMk (Level.substFn φ cvP.levelParams [.zero, .zero])) :=
    Denotes.const hfP (by simp [ConstantInfo.toConstantVal, hlP])
  have hrhs : Denotes M.cval env φ ρ2
      (prodMkK lk (.const tk.ty []) (.const tk.ty [])
        (of64K tk (natBinK .mod (natBinK .mul (natBinK .mod (.bvar 1) (litE size64))
          (natBinK .mod (.bvar 0) (litE size64))) (litE size64)))
        (of64K tk (natBinK .div (natBinK .mul (natBinK .mod (.bvar 1) (litE size64))
          (natBinK .mod (.bvar 0) (litE size64))) (litE size64))))
      (prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval tk.ty φ)
        (app (M.cval tk.ofNat φ) (litSet M φ ((x * y) % size64)))
        (app (M.cval tk.ofNat φ) (litSet M φ ((x * y) / size64)))) := by
    simp only [prodMkK, prodV, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    exact .app (.app (.app (.app hmkD (hty.den M φ ρ2)) (hty.den M φ ρ2)) hloD) hhiD
  have heq := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
  rw [heq, hofN, hofN]
  have hloLt : (x * y) % size64 < size64 := Nat.mod_lt _ (Width.size_pos .w64)
  have hhiLt : (x * y) / size64 < size64 := by
    have hsz : Width.w64.size = size64 := rfl
    rw [Nat.div_lt_iff_lt_mul (Width.size_pos .w64), hsz]
    have h1 : x * y ≤ (size64 - 1) * (size64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have hpos : 0 < size64 := Width.size_pos .w64
    have h3 : (size64 - 1) * (size64 - 1) < size64 * size64 := by
      have h2 : (size64 - 1) * (size64 - 1) ≤ (size64 - 1) * size64 :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (size64 - 1) * size64 + size64 = size64 * size64 := by
        rw [Nat.sub_mul, Nat.one_mul]
        have := Nat.le_mul_of_pos_left size64 hpos
        omega
      omega
    omega
  rw [Nat.mod_eq_of_lt hloLt, Nat.mod_eq_of_lt hhiLt]

/-- **`mulWide64` matches `IxCC.BigNat.mulWide64` directly in every `Ix.Kernel.Model`.** -/
theorem mulWide64_accel_bignat (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys} {kB kR kS kc kThm : KKey}
    {cvP : ConstantVal .anon} (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .mulWide64) (φ : LevelParam → Nat) (a b : UInt64) :
    app (app (M.cval kc φ) (towV M tk 64 size64 φ a.toNat)) (towV M tk 64 size64 φ b.toNat) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval tk.ty φ)
        (towV M tk 64 size64 φ (IxCC.BigNat.mulWide64 a b).1.toNat)
        (towV M tk 64 size64 φ (IxCC.BigNat.mulWide64 a b).2.toNat) := by
  rw [mulWide64_accel M hacc hN hE hBr hfP hlP hst φ
    (IxCC.BigNat.uint64_toNat_lt a) (IxCC.BigNat.uint64_toNat_lt b)]
  have h1 := LimbOp.mulWide64_lo_conservative a b
  have h2 := LimbOp.mulWide64_hi_conservative a b
  simp only [WordOp.eval, WordResult.val] at h1 h2
  rw [h1, h2]

/-- **3. `divWide64` adequacy over `Ix.Kernel.Model`**: for all `hi lo d < 2 ^ 64` with `hi < d`,
`divWide64` applied to `(towV hi, towV lo, towV d, pt)` equals `Prod.mk UInt64 UInt64 (towV q) (towV r)`. -/
theorem divWide64_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hE : EqBasis env)
    {tk : TowKeys} {lk : LimbKeys} {kB kR kS kc kThm : KKey} {cvP : ConstantVal .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .divWide64) (φ : LevelParam → Nat)
    {hi lo d : Nat} (hhi : hi < size64) (hlo : lo < size64) (hd : d < size64) (hlt : hi < d) :
    [towV M tk 64 size64 φ hi, towV M tk 64 size64 φ lo, towV M tk 64 size64 φ d, pt].foldl app
      (M.cval kc φ) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval tk.ty φ)
        (towV M tk 64 size64 φ ((hi * size64 + lo) / d))
        (towV M tk 64 size64 φ ((hi * size64 + lo) % d)) := by
  have hF := natFacts M hN φ
  obtain ⟨hkc, hty, hops, cvT, pfT, ms, hfT, htT⟩ := hst
  have hofN : ∀ a, app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk 64 size64 φ (a % size64) :=
    ofNat_tow M hacc hN hE hBr φ
  have hofD : ∀ ρ, Denotes M.cval env φ ρ (.const tk.ofNat []) (M.cval tk.ofNat φ) :=
    hBr.den M (by simp) φ
  let ρ0 : BVarIdx → V := fun _ => empty
  obtain ⟨TT, hTT, hm⟩ := mem_key M hfT φ ρ0
  simp only [ConstantInfo.toConstantVal, htT, limbStmtK, eqK] at hTT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF hi)
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 (lit_mem M hF lo)
  obtain ⟨B3, hB3, hm3⟩ := app_mem_den_pi hB2 ((hF.natD _ _).mpr rfl) hm2 (lit_mem M hF d)
  let ρ3 : BVarIdx → V := push (litSet M φ d) (push (litSet M φ lo) (push (litSet M φ hi) ρ0))
  have hhiM0 : Denotes M.cval env φ ρ3 (natBinK .mod (.bvar 2) (litE size64)) (litSet M φ hi) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ3) (i := 2) (a := hi) (.bvar (i := 2))
    rwa [Nat.mod_eq_of_lt hhi] at h
  have hdM0 : Denotes M.cval env φ ρ3 (natBinK .mod (.bvar 0) (litE size64)) (litSet M φ d) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ3) (i := 0) (a := d) (.bvar (i := 0))
    rwa [Nat.mod_eq_of_lt hd] at h
  have hboundD : Denotes M.cval env φ ρ3
      (leApp tk.le (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
        (natBinK .mod (.bvar 0) (litE size64)))
      (app (app (M.cval tk.le φ) (litSet M φ (hi + 1))) (litSet M φ d)) :=
    .app (.app (den_le_const M hBr.le ρ3) (.app ((hF.succD _ _).mpr rfl) hhiM0)) hdM0
  have hpt : (pt : V) ∈ˢ app (app (M.cval tk.le φ) (litSet M φ (hi + 1))) (litSet M φ d) :=
    pt_mem_natLe M hN hBr.le φ hlt
  obtain ⟨B4, hB4, hm4⟩ := app_mem_den_pi hB3 hboundD hm3 hpt
  obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hB4 hm4
  let ρ4 : BVarIdx → V := push (pt : V) ρ3
  have hhiT : app (M.cval tk.ofNat φ) (litSet M φ hi) = towV M tk 64 size64 φ hi := by
    rw [hofN hi, Nat.mod_eq_of_lt hhi]
  have hloT : app (M.cval tk.ofNat φ) (litSet M φ lo) = towV M tk 64 size64 φ lo := by
    rw [hofN lo, Nat.mod_eq_of_lt hlo]
  have hdT : app (M.cval tk.ofNat φ) (litSet M φ d) = towV M tk 64 size64 φ d := by
    rw [hofN d, Nat.mod_eq_of_lt hd]
  have hlhs : Denotes M.cval env φ ρ4
      (Expr.mkAppN (.const kc []) [of64K tk (.bvar 3), of64K tk (.bvar 2), of64K tk (.bvar 1), .bvar 0])
      ([towV M tk 64 size64 φ hi, towV M tk 64 size64 φ lo, towV M tk 64 size64 φ d, pt].foldl app
        (M.cval kc φ)) := by
    simp only [Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    rw [← hhiT, ← hloT, ← hdT]
    exact .app (.app (.app (.app (hkc.den M φ ρ4) (.app (hofD ρ4) (.bvar (i := 3))))
      (.app (hofD ρ4) (.bvar (i := 2)))) (.app (hofD ρ4) (.bvar (i := 1)))) (.bvar (i := 0))
  have hhiM : Denotes M.cval env φ ρ4 (natBinK .mod (.bvar 3) (litE size64)) (litSet M φ hi) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ4) (i := 3) (a := hi) (.bvar (i := 3))
    rwa [Nat.mod_eq_of_lt hhi] at h
  have hloM : Denotes M.cval env φ ρ4 (natBinK .mod (.bvar 2) (litE size64)) (litSet M φ lo) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ4) (i := 2) (a := lo) (.bvar (i := 2))
    rwa [Nat.mod_eq_of_lt hlo] at h
  have hdM : Denotes M.cval env φ ρ4 (natBinK .mod (.bvar 1) (litE size64)) (litSet M φ d) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ4) (i := 1) (a := d) (.bvar (i := 1))
    rwa [Nat.mod_eq_of_lt hd] at h
  have hmulK : KeyStored env (primKey .mul) := hops .mul (by simp [limbPrimOps])
  have haddK : KeyStored env (primKey .add) := hops .add (by simp [limbPrimOps])
  have hdivK : KeyStored env (primKey .div) := hops .div (by simp [limbPrimOps])
  have hmodK : KeyStored env (primKey .mod) := hops .mod (by simp [limbPrimOps])
  have hmulD : Denotes M.cval env φ ρ4
      (natBinK .mul (natBinK .mod (.bvar 3) (litE size64)) (litE size64))
      (litSet M φ (hi * size64)) := by
    rw [← natMul_accel M hacc hN hmulK φ hi size64]
    exact .app (.app (hmulK.den M φ ρ4) hhiM) ((lit_den M hF ρ4 size64 _).mpr rfl)
  have hnumD : Denotes M.cval env φ ρ4
      (natBinK .add (natBinK .mul (natBinK .mod (.bvar 3) (litE size64)) (litE size64))
        (natBinK .mod (.bvar 2) (litE size64)))
      (litSet M φ (hi * size64 + lo)) := by
    rw [← natAdd_accel M hacc hN haddK φ (hi * size64) lo]
    exact .app (.app (haddK.den M φ ρ4) hmulD) hloM
  have hqD : Denotes M.cval env φ ρ4
      (of64K tk (natBinK .div
        (natBinK .add (natBinK .mul (natBinK .mod (.bvar 3) (litE size64)) (litE size64))
          (natBinK .mod (.bvar 2) (litE size64)))
        (natBinK .mod (.bvar 1) (litE size64))))
      (app (M.cval tk.ofNat φ) (litSet M φ ((hi * size64 + lo) / d))) := by
    refine .app (hofD ρ4) ?_
    rw [← natDiv_accel M hacc hN hdivK φ (hi * size64 + lo) d]
    exact .app (.app (hdivK.den M φ ρ4) hnumD) hdM
  have hrD : Denotes M.cval env φ ρ4
      (of64K tk (natBinK .mod
        (natBinK .add (natBinK .mul (natBinK .mod (.bvar 3) (litE size64)) (litE size64))
          (natBinK .mod (.bvar 2) (litE size64)))
        (natBinK .mod (.bvar 1) (litE size64))))
      (app (M.cval tk.ofNat φ) (litSet M φ ((hi * size64 + lo) % d))) := by
    refine .app (hofD ρ4) ?_
    rw [← natMod_accel M hacc hN hmodK φ (hi * size64 + lo) d]
    exact .app (.app (hmodK.den M φ ρ4) hnumD) hdM
  have hmkD : Denotes M.cval env φ ρ4 (.const lk.prodMk [.zero, .zero])
      (M.cval lk.prodMk (Level.substFn φ cvP.levelParams [.zero, .zero])) :=
    Denotes.const hfP (by simp [ConstantInfo.toConstantVal, hlP])
  have hrhs : Denotes M.cval env φ ρ4
      (prodMkK lk (.const tk.ty []) (.const tk.ty [])
        (of64K tk (natBinK .div
          (natBinK .add (natBinK .mul (natBinK .mod (.bvar 3) (litE size64)) (litE size64))
            (natBinK .mod (.bvar 2) (litE size64)))
          (natBinK .mod (.bvar 1) (litE size64))))
        (of64K tk (natBinK .mod
          (natBinK .add (natBinK .mul (natBinK .mod (.bvar 3) (litE size64)) (litE size64))
            (natBinK .mod (.bvar 2) (litE size64)))
          (natBinK .mod (.bvar 1) (litE size64)))))
      (prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval tk.ty φ)
        (app (M.cval tk.ofNat φ) (litSet M φ ((hi * size64 + lo) / d)))
        (app (M.cval tk.ofNat φ) (litSet M φ ((hi * size64 + lo) % d)))) := by
    simp only [prodMkK, prodV, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    exact .app (.app (.app (.app hmkD (hty.den M φ ρ4)) (hty.den M φ ρ4)) hqD) hrD
  have heq := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
  rw [heq, hofN, hofN]
  have hdPos : 0 < d := by omega
  have hqLt : (hi * size64 + lo) / d < size64 := by
    rw [Nat.div_lt_iff_lt_mul hdPos]
    have hle : (hi + 1) * size64 ≤ d * size64 := Nat.mul_le_mul_right size64 hlt
    rw [Nat.add_mul, Nat.one_mul] at hle
    rw [Nat.mul_comm size64 d]
    omega
  have hrLt : (hi * size64 + lo) % d < size64 := Nat.lt_trans (Nat.mod_lt _ hdPos) hd
  rw [Nat.mod_eq_of_lt hqLt, Nat.mod_eq_of_lt hrLt]

/-- **`divWide64` matches `IxCC.BigNat.divWide64` directly in every `Ix.Kernel.Model`.** -/
theorem divWide64_accel_bignat (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys} {kB kR kS kc kThm : KKey}
    {cvP : ConstantVal .anon} (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .divWide64) (φ : LevelParam → Nat)
    (hi lo d : UInt64) (h : hi < d) :
    [towV M tk 64 size64 φ hi.toNat, towV M tk 64 size64 φ lo.toNat,
     towV M tk 64 size64 φ d.toNat, pt].foldl app (M.cval kc φ) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval tk.ty φ)
        (towV M tk 64 size64 φ (IxCC.BigNat.divWide64 hi lo d h).1.toNat)
        (towV M tk 64 size64 φ (IxCC.BigNat.divWide64 hi lo d h).2.toNat) := by
  rw [divWide64_accel M hacc hN hE hBr hfP hlP hst φ
    (IxCC.BigNat.uint64_toNat_lt hi) (IxCC.BigNat.uint64_toNat_lt lo)
    (IxCC.BigNat.uint64_toNat_lt d) (UInt64.lt_iff_toNat_lt.mp h)]
  rw [IxCC.BigNat.divWide64_fst hi lo d h, IxCC.BigNat.divWide64_snd hi lo d h]
  rfl

/-- **4. `addCarry64` adequacy over `Ix.Kernel.Model`**: for all `x y < 2 ^ 64` and `c : Bool`,
`addCarry64` applied to `(towV x, towV y, boolSet c)` equals
`Prod.mk UInt64 Bool (towV ((x + y + c.toNat) % 2^64)) (boolSet (decide (2^64 ≤ x + y + c.toNat)))`. -/
theorem addCarry64_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys}
    {kB kR kS kBF kBT kc kThm : KKey} {cvP : ConstantVal .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hBN : BoolToNatStored env lk.boolToNat kBF kBT)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .addCarry64) (φ : LevelParam → Nat)
    {x y : Nat} (hx : x < size64) (hy : y < size64) (c : Bool) :
    [towV M tk 64 size64 φ x, towV M tk 64 size64 φ y, boolSet M φ c].foldl app (M.cval kc φ) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval boolKey φ)
        (towV M tk 64 size64 φ ((x + y + c.toNat) % size64))
        (boolSet M φ (decide (size64 ≤ x + y + c.toNat))) := by
  have hF := natFacts M hN φ
  obtain ⟨hkc, hty, hops, cvT, pfT, ms, hfT, htT⟩ := hst
  have hofN : ∀ a, app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk 64 size64 φ (a % size64) :=
    ofNat_tow M hacc hN hE hBr φ
  have hofD : ∀ ρ, Denotes M.cval env φ ρ (.const tk.ofNat []) (M.cval tk.ofNat φ) :=
    hBr.den M (by simp) φ
  let ρ0 : BVarIdx → V := fun _ => empty
  obtain ⟨TT, hTT, hm⟩ := mem_key M hfT φ ρ0
  simp only [ConstantInfo.toConstantVal, htT, limbStmtK, eqK] at hTT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF x)
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 (lit_mem M hF y)
  obtain ⟨B3, hB3, hm3⟩ := app_mem_den_pi hB2 (bool_den M hB φ _) hm2 (boolLit_mem M hB φ c)
  obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hB3 hm3
  let ρ3 : BVarIdx → V := push (boolSet M φ c) (push (litSet M φ y) (push (litSet M φ x) ρ0))
  have hxT : app (M.cval tk.ofNat φ) (litSet M φ x) = towV M tk 64 size64 φ x := by
    rw [hofN x, Nat.mod_eq_of_lt hx]
  have hyT : app (M.cval tk.ofNat φ) (litSet M φ y) = towV M tk 64 size64 φ y := by
    rw [hofN y, Nat.mod_eq_of_lt hy]
  have hlhs : Denotes M.cval env φ ρ3
      (Expr.mkAppN (.const kc []) [of64K tk (.bvar 2), of64K tk (.bvar 1), .bvar 0])
      ([towV M tk 64 size64 φ x, towV M tk 64 size64 φ y, boolSet M φ c].foldl app (M.cval kc φ)) := by
    simp only [Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    rw [← hxT, ← hyT]
    exact .app (.app (.app (hkc.den M φ ρ3) (.app (hofD ρ3) (.bvar (i := 2))))
      (.app (hofD ρ3) (.bvar (i := 1)))) (.bvar (i := 0))
  have hmodX : Denotes M.cval env φ ρ3 (natBinK .mod (.bvar 2) (litE size64)) (litSet M φ x) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ3) (i := 2) (a := x) (.bvar (i := 2))
    rwa [Nat.mod_eq_of_lt hx] at h
  have hmodY : Denotes M.cval env φ ρ3 (natBinK .mod (.bvar 1) (litE size64)) (litSet M φ y) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ3) (i := 1) (a := y) (.bvar (i := 1))
    rwa [Nat.mod_eq_of_lt hy] at h
  have hcnD : Denotes M.cval env φ ρ3 (.app (.const lk.boolToNat []) (.bvar 0))
      (litSet M φ c.toNat) := by
    rw [← boolToNat_accel M hN hB hE hBN φ c]
    exact .app (hBN.key.den M φ ρ3) (.bvar (i := 0))
  have haddK : KeyStored env (primKey .add) := hops .add (by simp [limbPrimOps])
  have hbleK : KeyStored env (primKey .ble) := hops .ble (by simp [limbPrimOps])
  have hxyD : Denotes M.cval env φ ρ3
      (natBinK .add (natBinK .mod (.bvar 2) (litE size64)) (natBinK .mod (.bvar 1) (litE size64)))
      (litSet M φ (x + y)) := by
    rw [← natAdd_accel M hacc hN haddK φ x y]
    exact .app (.app (haddK.den M φ ρ3) hmodX) hmodY
  have hsumD : Denotes M.cval env φ ρ3
      (natBinK .add (natBinK .add (natBinK .mod (.bvar 2) (litE size64))
        (natBinK .mod (.bvar 1) (litE size64))) (.app (.const lk.boolToNat []) (.bvar 0)))
      (litSet M φ (x + y + c.toNat)) := by
    rw [← natAdd_accel M hacc hN haddK φ (x + y) c.toNat]
    exact .app (.app (haddK.den M φ ρ3) hxyD) hcnD
  have hcarryD : Denotes M.cval env φ ρ3
      (natBinK .ble (litE size64)
        (natBinK .add (natBinK .add (natBinK .mod (.bvar 2) (litE size64))
          (natBinK .mod (.bvar 1) (litE size64))) (.app (.const lk.boolToNat []) (.bvar 0))))
      (boolSet M φ (decide (size64 ≤ x + y + c.toNat))) := by
    rw [← natCmp_accel M hacc hN hB (.inr rfl) hbleK φ size64 (x + y + c.toNat)]
    exact .app (.app (hbleK.den M φ ρ3) ((lit_den M hF ρ3 size64 _).mpr rfl)) hsumD
  have hmkD : Denotes M.cval env φ ρ3 (.const lk.prodMk [.zero, .zero])
      (M.cval lk.prodMk (Level.substFn φ cvP.levelParams [.zero, .zero])) :=
    Denotes.const hfP (by simp [ConstantInfo.toConstantVal, hlP])
  have hrhs : Denotes M.cval env φ ρ3
      (prodMkK lk (.const tk.ty []) boolK
        (of64K tk (natBinK .add (natBinK .add (natBinK .mod (.bvar 2) (litE size64))
          (natBinK .mod (.bvar 1) (litE size64))) (.app (.const lk.boolToNat []) (.bvar 0))))
        (natBinK .ble (litE size64)
          (natBinK .add (natBinK .add (natBinK .mod (.bvar 2) (litE size64))
            (natBinK .mod (.bvar 1) (litE size64))) (.app (.const lk.boolToNat []) (.bvar 0)))))
      (prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval boolKey φ)
        (app (M.cval tk.ofNat φ) (litSet M φ (x + y + c.toNat)))
        (boolSet M φ (decide (size64 ≤ x + y + c.toNat)))) := by
    simp only [prodMkK, prodV, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    exact .app (.app (.app (.app hmkD (hty.den M φ ρ3)) (bool_den M hB φ ρ3))
      (.app (hofD ρ3) hsumD)) hcarryD
  have heq := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
  rw [heq, hofN]

/-- **`addCarry64` matches `IxCC.BigNat.addCarry64` directly in every `Ix.Kernel.Model`.** -/
theorem addCarry64_accel_bignat (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys}
    {kB kR kS kBF kBT kc kThm : KKey} {cvP : ConstantVal .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hBN : BoolToNatStored env lk.boolToNat kBF kBT)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .addCarry64) (φ : LevelParam → Nat)
    (a b : UInt64) (c : Bool) :
    [towV M tk 64 size64 φ a.toNat, towV M tk 64 size64 φ b.toNat, boolSet M φ c].foldl app
      (M.cval kc φ) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval boolKey φ)
        (towV M tk 64 size64 φ (IxCC.BigNat.addCarry64 a b c).1.toNat)
        (boolSet M φ (IxCC.BigNat.addCarry64 a b c).2) := by
  rw [addCarry64_accel M hacc hN hB hE hBr hBN hfP hlP hst φ
    (IxCC.BigNat.uint64_toNat_lt a) (IxCC.BigNat.uint64_toNat_lt b) c]
  simp only [IxCC.BigNat.addCarry64, size64, Width.size, Width.bits, UInt64.toNat_ofNat']
  rfl

/-- **5. `subBorrow64` adequacy over `Ix.Kernel.Model`**: for all `x y < 2 ^ 64` and `b : Bool`,
`subBorrow64` applied to `(towV x, towV y, boolSet b)` equals
`Prod.mk UInt64 Bool (towV diff) (boolSet (decide (x < y + b.toNat)))`. -/
theorem subBorrow64_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys}
    {kB kR kS kBF kBT kCT kCF kc kThm : KKey} {cvP : ConstantVal .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hBN : BoolToNatStored env lk.boolToNat kBF kBT)
    (hC : CondNatStored env lk.cond kCT kCF)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .subBorrow64) (φ : LevelParam → Nat)
    {x y : Nat} (hx : x < size64) (hy : y < size64) (b : Bool) :
    [towV M tk 64 size64 φ x, towV M tk 64 size64 φ y, boolSet M φ b].foldl app (M.cval kc φ) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval boolKey φ)
        (towV M tk 64 size64 φ (if x < y + b.toNat then size64 + x - (y + b.toNat) else x - (y + b.toNat)))
        (boolSet M φ (decide (x < y + b.toNat))) := by
  have hF := natFacts M hN φ
  obtain ⟨hkc, hty, hops, cvT, pfT, ms, hfT, htT⟩ := hst
  obtain ⟨ciC, hfC, hlC⟩ := hC.key
  have hofN : ∀ a, app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk 64 size64 φ (a % size64) :=
    ofNat_tow M hacc hN hE hBr φ
  have hofD : ∀ ρ, Denotes M.cval env φ ρ (.const tk.ofNat []) (M.cval tk.ofNat φ) :=
    hBr.den M (by simp) φ
  let ρ0 : BVarIdx → V := fun _ => empty
  obtain ⟨TT, hTT, hm⟩ := mem_key M hfT φ ρ0
  simp only [ConstantInfo.toConstantVal, htT, limbStmtK, eqK] at hTT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF x)
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 ((hF.natD _ _).mpr rfl) hm1 (lit_mem M hF y)
  obtain ⟨B3, hB3, hm3⟩ := app_mem_den_pi hB2 (bool_den M hB φ _) hm2 (boolLit_mem M hB φ b)
  obtain ⟨v, hv1, hv2⟩ := eq_of_inhabited M hE hB3 hm3
  let ρ3 : BVarIdx → V := push (boolSet M φ b) (push (litSet M φ y) (push (litSet M φ x) ρ0))
  have hxT : app (M.cval tk.ofNat φ) (litSet M φ x) = towV M tk 64 size64 φ x := by
    rw [hofN x, Nat.mod_eq_of_lt hx]
  have hyT : app (M.cval tk.ofNat φ) (litSet M φ y) = towV M tk 64 size64 φ y := by
    rw [hofN y, Nat.mod_eq_of_lt hy]
  have hlhs : Denotes M.cval env φ ρ3
      (Expr.mkAppN (.const kc []) [of64K tk (.bvar 2), of64K tk (.bvar 1), .bvar 0])
      ([towV M tk 64 size64 φ x, towV M tk 64 size64 φ y, boolSet M φ b].foldl app (M.cval kc φ)) := by
    simp only [Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    rw [← hxT, ← hyT]
    exact .app (.app (.app (hkc.den M φ ρ3) (.app (hofD ρ3) (.bvar (i := 2))))
      (.app (hofD ρ3) (.bvar (i := 1)))) (.bvar (i := 0))
  have hmodX : Denotes M.cval env φ ρ3 (natBinK .mod (.bvar 2) (litE size64)) (litSet M φ x) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ3) (i := 2) (a := x) (.bvar (i := 2))
    rwa [Nat.mod_eq_of_lt hx] at h
  have hmodY : Denotes M.cval env φ ρ3 (natBinK .mod (.bvar 1) (litE size64)) (litSet M φ y) := by
    have h := den_modK M hacc hN hBr (φ := φ) (ρ := ρ3) (i := 1) (a := y) (.bvar (i := 1))
    rwa [Nat.mod_eq_of_lt hy] at h
  have hbnD : Denotes M.cval env φ ρ3 (.app (.const lk.boolToNat []) (.bvar 0))
      (litSet M φ b.toNat) := by
    rw [← boolToNat_accel M hN hB hE hBN φ b]
    exact .app (hBN.key.den M φ ρ3) (.bvar (i := 0))
  have haddK : KeyStored env (primKey .add) := hops .add (by simp [limbPrimOps])
  have hbleK : KeyStored env (primKey .ble) := hops .ble (by simp [limbPrimOps])
  have hsubK : KeyStored env (primKey .sub) := hops .sub (by simp [limbPrimOps])
  have hsubAmtD : Denotes M.cval env φ ρ3
      (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0)))
      (litSet M φ (y + b.toNat)) := by
    rw [← natAdd_accel M hacc hN haddK φ y b.toNat]
    exact .app (.app (haddK.den M φ ρ3) hmodY) hbnD
  have hsuccXD : Denotes M.cval env φ ρ3
      (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
      (litSet M φ (x + 1)) :=
    .app ((hF.succD _ _).mpr rfl) hmodX
  have hborEq : decide (x + 1 ≤ y + b.toNat) = decide (x < y + b.toNat) := rfl
  have hborD : Denotes M.cval env φ ρ3
      (natBinK .ble (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
        (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
      (boolSet M φ (decide (x < y + b.toNat))) := by
    rw [← hborEq, ← natCmp_accel M hacc hN hB (.inr rfl) hbleK φ (x + 1) (y + b.toNat)]
    exact .app (.app (hbleK.den M φ ρ3) hsuccXD) hsubAmtD
  have haddMXD : Denotes M.cval env φ ρ3
      (natBinK .add (litE size64) (natBinK .mod (.bvar 2) (litE size64)))
      (litSet M φ (size64 + x)) := by
    rw [← natAdd_accel M hacc hN haddK φ size64 x]
    exact .app (.app (haddK.den M φ ρ3) ((lit_den M hF ρ3 size64 _).mpr rfl)) hmodX
  have hhiDiffD : Denotes M.cval env φ ρ3
      (natBinK .sub (natBinK .add (litE size64) (natBinK .mod (.bvar 2) (litE size64)))
        (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
      (litSet M φ (size64 + x - (y + b.toNat))) := by
    rw [← natSub_accel M hacc hN hsubK φ (size64 + x) (y + b.toNat)]
    exact .app (.app (hsubK.den M φ ρ3) haddMXD) hsubAmtD
  have hloDiffD : Denotes M.cval env φ ρ3
      (natBinK .sub (natBinK .mod (.bvar 2) (litE size64))
        (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
      (litSet M φ (x - (y + b.toNat))) := by
    rw [← natSub_accel M hacc hN hsubK φ x (y + b.toNat)]
    exact .app (.app (hsubK.den M φ ρ3) hmodX) hsubAmtD
  have hcondK : Denotes M.cval env φ ρ3 (.const lk.cond [.zero])
      (M.cval lk.cond (Level.substFn φ ciC.toConstantVal.levelParams [.zero])) :=
    Denotes.const hfC (by simp [hlC])
  have hcondVal := condNat_accel M hN hB hE hC hfC φ (decide (x < y + b.toNat))
    (lit_mem M hF (size64 + x - (y + b.toNat))) (lit_mem M hF (x - (y + b.toNat)))
  let diffN : Nat := if x < y + b.toNat then size64 + x - (y + b.toNat) else x - (y + b.toNat)
  have hdiffD : Denotes M.cval env φ ρ3
      (condNatK lk
        (natBinK .ble (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
          (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
        (natBinK .sub (natBinK .add (litE size64) (natBinK .mod (.bvar 2) (litE size64)))
          (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
        (natBinK .sub (natBinK .mod (.bvar 2) (litE size64))
          (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0)))))
      (litSet M φ diffN) := by
    have h0 : Denotes M.cval env φ ρ3
        (condNatK lk
          (natBinK .ble (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
            (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
          (natBinK .sub (natBinK .add (litE size64) (natBinK .mod (.bvar 2) (litE size64)))
            (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
          (natBinK .sub (natBinK .mod (.bvar 2) (litE size64))
            (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0)))))
        ([M.cval natName φ, boolSet M φ (decide (x < y + b.toNat)),
          litSet M φ (size64 + x - (y + b.toNat)), litSet M φ (x - (y + b.toNat))].foldl app
          (M.cval lk.cond (Level.substFn φ ciC.toConstantVal.levelParams [.zero]))) := by
      simp only [condNatK, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
      exact .app (.app (.app (.app hcondK ((hF.natD _ _).mpr rfl)) hborD) hhiDiffD) hloDiffD
    rw [hcondVal] at h0
    by_cases hlt : x < y + b.toNat
    · simp only [diffN, hlt, decide_true, ↓reduceIte] at h0 ⊢; exact h0
    · simp only [diffN, hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at h0 ⊢; exact h0
  have hmkD : Denotes M.cval env φ ρ3 (.const lk.prodMk [.zero, .zero])
      (M.cval lk.prodMk (Level.substFn φ cvP.levelParams [.zero, .zero])) :=
    Denotes.const hfP (by simp [ConstantInfo.toConstantVal, hlP])
  have hrhs : Denotes M.cval env φ ρ3
      (prodMkK lk (.const tk.ty []) boolK
        (of64K tk (condNatK lk
          (natBinK .ble (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
            (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
          (natBinK .sub (natBinK .add (litE size64) (natBinK .mod (.bvar 2) (litE size64)))
            (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))
          (natBinK .sub (natBinK .mod (.bvar 2) (litE size64))
            (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0))))))
        (natBinK .ble (.app (.const natSuccName []) (natBinK .mod (.bvar 2) (litE size64)))
          (natBinK .add (natBinK .mod (.bvar 1) (litE size64)) (.app (.const lk.boolToNat []) (.bvar 0)))))
      (prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval boolKey φ)
        (app (M.cval tk.ofNat φ) (litSet M φ diffN))
        (boolSet M φ (decide (x < y + b.toNat)))) := by
    simp only [prodMkK, prodV, Expr.mkAppN, List.foldl_cons, List.foldl_nil]
    exact .app (.app (.app (.app hmkD (hty.den M φ ρ3)) (bool_den M hB φ ρ3))
      (.app (hofD ρ3) hdiffD)) hborD
  have heq := (Denotes_functional hv1 hlhs).symm.trans (Denotes_functional hv2 hrhs)
  rw [heq, hofN]
  have hbLe : b.toNat ≤ 1 := by cases b <;> decide
  have hdiffLt : diffN < size64 := by
    dsimp only [diffN]
    split <;> omega
  rw [Nat.mod_eq_of_lt hdiffLt]

/-- **`subBorrow64` matches `IxCC.BigNat.subBorrow64` directly in every `Ix.Kernel.Model`.** -/
theorem subBorrow64_accel_bignat (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) {tk : TowKeys} {lk : LimbKeys}
    {kB kR kS kBF kBT kCT kCF kc kThm : KKey} {cvP : ConstantVal .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hBN : BoolToNatStored env lk.boolToNat kBF kBT)
    (hC : CondNatStored env lk.cond kCT kCF)
    (hfP : env.find? lk.prodMk = some (.ctorInfo cvP 2 2)) (hlP : cvP.levelParams.length = 2)
    (hst : LimbStmt env tk lk kc kThm .subBorrow64) (φ : LevelParam → Nat)
    (a b : UInt64) (bIn : Bool) :
    [towV M tk 64 size64 φ a.toNat, towV M tk 64 size64 φ b.toNat, boolSet M φ bIn].foldl app
      (M.cval kc φ) =
      prodV M lk.prodMk cvP.levelParams φ (M.cval tk.ty φ) (M.cval boolKey φ)
        (towV M tk 64 size64 φ (IxCC.BigNat.subBorrow64 a b bIn).1.toNat)
        (boolSet M φ (IxCC.BigNat.subBorrow64 a b bIn).2) := by
  have ha := IxCC.BigNat.uint64_toNat_lt a
  have hb := IxCC.BigNat.uint64_toNat_lt b
  have hbi : bIn.toNat ≤ 1 := by cases bIn <;> decide
  rw [subBorrow64_accel M hacc hN hB hE hBr hBN hC hfP hlP hst φ ha hb bIn]
  simp only [IxCC.BigNat.subBorrow64, UInt64.toNat_ofNat', size64, Width.size, Width.bits]
  split <;> ·
    congr 2
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ## Extracting the 9 scalar `WordOp` limb components via `M.proj_law` -/

/-- Projection `.1` of a well-typed `Prod.mk.{0, 0} A B a b` yields `a` (`M.proj_law`). -/
theorem proj_prod_fst (M : Model V env) {lk : LimbKeys} (hP : ProdBasis env lk)
    {cvT : ConstantVal .anon} {caps : IndCaps .anon}
    (hfT : env.find? lk.prodTy = some (.indInfo cvT caps))
    {cvM : ConstantVal .anon} (hfM : env.find? lk.prodMk = some (.ctorInfo cvM 2 2))
    {e0 : ProjEntry .anon} (hp0 : env.findProj? lk.prodTy 0 = some e0)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {A B a b : V}
    (hfit : Fits M.cval env φ ρ (cvM.type.instantiateLevelParams cvM.levelParams [.zero, .zero])
      [A, B, a, b] σ R) :
    projVal M.cval lk.prodTy 0 e0 (prodV M lk.prodMk cvM.levelParams φ A B a b) = a := by
  obtain ⟨cvT', caps', hfT', hlT'⟩ := hP.prodTy
  obtain ⟨cvM', hfM', hlM'⟩ := hP.prodMk
  obtain ⟨e0', hp0', hec, hnp, hnf, hss⟩ := hP.proj0
  rw [hfT] at hfT'; cases hfT'
  rw [hfM] at hfM'; cases hfM'
  rw [hp0] at hp0'; cases hp0'
  obtain ⟨hlpT, cvC', hfC', hlpC, -, hlaw⟩ := M.proj_law lk.prodTy 0 e0 cvT caps hp0 hfT
  rw [hec, hnp, hnf, hfM] at hfC'; cases hfC'
  have hlen : ([.zero, .zero] : List Level).length = e0.levelParams.length := by
    rw [← hlpT, hlT']; rfl
  have hFT : Denotes M.cval env φ ρ (.const lk.prodTy [.zero, .zero])
      (M.cval lk.prodTy (Level.substFn φ cvT.levelParams [.zero, .zero])) :=
    Denotes.const hfT (by simp [ConstantInfo.toConstantVal, hlT'])
  have hKM : Denotes M.cval env φ ρ (.const e0.ctor [.zero, .zero])
      (M.cval lk.prodMk (Level.substFn φ cvM.levelParams [.zero, .zero])) := by
    rw [hec]; exact Denotes.const hfM (by simp [ConstantInfo.toConstantVal, hlM'])
  obtain ⟨hproj, -⟩ := hlaw [.zero, .zero] φ ρ _ _ hlen hFT hKM
  have hres := hproj (fun h0 => absurd h0 (hss _)) σ R [A, B, a, b] (by simp [hnp, hnf]) hfit
  simpa [prodV, hnp] using hres

/-- Projection `.2` of a well-typed `Prod.mk.{0, 0} A B a b` yields `b` (`M.proj_law`). -/
theorem proj_prod_snd (M : Model V env) {lk : LimbKeys} (hP : ProdBasis env lk)
    {cvT : ConstantVal .anon} {caps : IndCaps .anon}
    (hfT : env.find? lk.prodTy = some (.indInfo cvT caps))
    {cvM : ConstantVal .anon} (hfM : env.find? lk.prodMk = some (.ctorInfo cvM 2 2))
    {e1 : ProjEntry .anon} (hp1 : env.findProj? lk.prodTy 1 = some e1)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {A B a b : V}
    (hfit : Fits M.cval env φ ρ (cvM.type.instantiateLevelParams cvM.levelParams [.zero, .zero])
      [A, B, a, b] σ R) :
    projVal M.cval lk.prodTy 1 e1 (prodV M lk.prodMk cvM.levelParams φ A B a b) = b := by
  obtain ⟨cvT', caps', hfT', hlT'⟩ := hP.prodTy
  obtain ⟨cvM', hfM', hlM'⟩ := hP.prodMk
  obtain ⟨e1', hp1', hec, hnp, hnf, hss⟩ := hP.proj1
  rw [hfT] at hfT'; cases hfT'
  rw [hfM] at hfM'; cases hfM'
  rw [hp1] at hp1'; cases hp1'
  obtain ⟨hlpT, cvC', hfC', hlpC, -, hlaw⟩ := M.proj_law lk.prodTy 1 e1 cvT caps hp1 hfT
  rw [hec, hnp, hnf, hfM] at hfC'; cases hfC'
  have hlen : ([.zero, .zero] : List Level).length = e1.levelParams.length := by
    rw [← hlpT, hlT']; rfl
  have hFT : Denotes M.cval env φ ρ (.const lk.prodTy [.zero, .zero])
      (M.cval lk.prodTy (Level.substFn φ cvT.levelParams [.zero, .zero])) :=
    Denotes.const hfT (by simp [ConstantInfo.toConstantVal, hlT'])
  have hKM : Denotes M.cval env φ ρ (.const e1.ctor [.zero, .zero])
      (M.cval lk.prodMk (Level.substFn φ cvM.levelParams [.zero, .zero])) := by
    rw [hec]; exact Denotes.const hfM (by simp [ConstantInfo.toConstantVal, hlM'])
  obtain ⟨hproj, -⟩ := hlaw [.zero, .zero] φ ρ _ _ hlen hFT hKM
  have hres := hproj (fun h0 => absurd h0 (hss _)) σ R [A, B, a, b] (by simp [hnp, hnf]) hfit
  simpa [prodV, hnp] using hres

end Sem

/-! ## Decidable checkers and soundness proofs -/

section Check

variable (env : KEnv)

def boolBasisB : Bool :=
  (match env.find? boolKey with
    | some (.indInfo cv _) => decide (cv.levelParams = [])
    | _ => false) &&
  (match env.find? boolTrueName with
    | some (.ctorInfo cv 0 0) => decide (cv.levelParams = [] ∧ cv.type = boolK)
    | _ => false) &&
  (match env.find? boolFalseName with
    | some (.ctorInfo cv 0 0) => decide (cv.levelParams = [] ∧ cv.type = boolK)
    | _ => false)

def boolToNatB (kB2N kThmF kThmT : KKey) : Bool :=
  keyStoredB env kB2N &&
  (match env.find? kThmF with
    | some (.thmInfo cv _) => decide (cv.type = eqK natK (.app (.const kB2N []) (boolLitK false)) (litE 0))
    | _ => false) &&
  (match env.find? kThmT with
    | some (.thmInfo cv _) => decide (cv.type = eqK natK (.app (.const kB2N []) (boolLitK true)) (litE 1))
    | _ => false)

def condNatB (kCond kThmT kThmF : KKey) : Bool :=
  (match env.find? kCond with
    | some ci => decide (ci.toConstantVal.levelParams.length = 1)
    | none => false) &&
  (match env.find? kThmT with
    | some (.thmInfo cv _) =>
      let ms := piMetas 2 cv.type
      decide (cv.type = .forallE natK (.forallE natK (eqK natK
        (Expr.mkAppN (.const kCond [.zero]) [natK, boolLitK true, .bvar 1, .bvar 0]) (.bvar 1))
        (bmAt ms 1)) (bmAt ms 0))
    | _ => false) &&
  (match env.find? kThmF with
    | some (.thmInfo cv _) =>
      let ms := piMetas 2 cv.type
      decide (cv.type = .forallE natK (.forallE natK (eqK natK
        (Expr.mkAppN (.const kCond [.zero]) [natK, boolLitK false, .bvar 1, .bvar 0]) (.bvar 0))
        (bmAt ms 1)) (bmAt ms 0))
    | _ => false)

def log2StoredB (lk : LimbKeys) (kThm : KKey) : Bool :=
  (match env.find? lk.natLog2 with
    | some ci =>
      let ms := piMetas 1 ci.toConstantVal.type
      decide (ci.toConstantVal.levelParams = [] ∧ ci.toConstantVal.type = .forallE natK natK (bmAt ms 0))
    | none => false) &&
  keyStoredB env (primKey .ble) &&
  keyStoredB env (primKey .div) &&
  (match env.find? kThm with
    | some (.thmInfo cv _) =>
      let ms := piMetas 1 cv.type
      decide (cv.type = .forallE natK (eqK natK
        (.app (.const lk.natLog2 []) (.bvar 0))
        (condNatK lk (natBinK .ble (litE 2) (.bvar 0))
          (.app (.const natSuccName []) (.app (.const lk.natLog2 []) (natBinK .div (.bvar 0) (litE 2))))
          (litE 0))) (bmAt ms 0))
    | _ => false)

def prodProjEntryB (e : ProjEntry .anon) (kMk : KKey) : Bool :=
  decide (e.ctor = kMk ∧ e.numParams = 2 ∧ e.numFields = 2) &&
    match e.structSort with
    | .succ _ => true
    | _ => false

def prodBasisB (lk : LimbKeys) : Bool :=
  (match env.find? lk.prodTy with
    | some (.indInfo cv _) => decide (cv.levelParams.length = 2)
    | _ => false) &&
  (match env.find? lk.prodMk with
    | some (.ctorInfo cv 2 2) => decide (cv.levelParams.length = 2)
    | _ => false) &&
  (match env.findProj? lk.prodTy 0 with
    | some e => prodProjEntryB e lk.prodMk
    | none => false) &&
  (match env.findProj? lk.prodTy 1 with
    | some e => prodProjEntryB e lk.prodMk
    | none => false)

def limbStmtB (tk : TowKeys) (lk : LimbKeys) (kc kThm : KKey) (op : LimbOp) : Bool :=
  keyStoredB env kc &&
  keyStoredB env tk.ty &&
  (limbPrimOps op).all (fun o => keyStoredB env (primKey o)) &&
  match env.find? kThm with
  | some (.thmInfo cv _) =>
    let ms := piMetas op.srcArity cv.type
    decide (cv.type = limbStmtK tk lk kc ms op)
  | _ => false

end Check

section CheckSound

variable {env : KEnv}

theorem boolBasis_of_check (h : boolBasisB env = true) : BoolBasis env := by
  simp only [boolBasisB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · split at h1
    · rename_i cv caps hf; exact ⟨cv, caps, hf, of_decide_eq_true h1⟩
    · cases h1
  · split at h2
    · rename_i cv hf
      obtain ⟨hl, ht⟩ := of_decide_eq_true h2
      exact ⟨cv, hf, hl, ht⟩
    · cases h2
  · split at h3
    · rename_i cv hf
      obtain ⟨hl, ht⟩ := of_decide_eq_true h3
      exact ⟨cv, hf, hl, ht⟩
    · cases h3

theorem boolToNat_of_check {kB2N kThmF kThmT : KKey}
    (h : boolToNatB env kB2N kThmF kThmT = true) : BoolToNatStored env kB2N kThmF kThmT := by
  simp only [boolToNatB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨keyStored_of h1, ?_, ?_⟩
  · split at h2
    · rename_i cv pf hf; exact ⟨cv, pf, hf, of_decide_eq_true h2⟩
    · cases h2
  · split at h3
    · rename_i cv pf hf; exact ⟨cv, pf, hf, of_decide_eq_true h3⟩
    · cases h3

theorem condNat_of_check {kCond kThmT kThmF : KKey}
    (h : condNatB env kCond kThmT kThmF = true) : CondNatStored env kCond kThmT kThmF := by
  simp only [condNatB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · split at h1
    · rename_i ci hf; exact ⟨ci, hf, of_decide_eq_true h1⟩
    · cases h1
  · split at h2
    · rename_i cv pf hf; exact ⟨cv, pf, _, _, hf, of_decide_eq_true h2⟩
    · cases h2
  · split at h3
    · rename_i cv pf hf; exact ⟨cv, pf, _, _, hf, of_decide_eq_true h3⟩
    · cases h3

theorem log2Stored_of_check {lk : LimbKeys} {kThm : KKey}
    (h : log2StoredB env lk kThm = true) : Log2Stored env lk kThm := by
  simp only [log2StoredB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, keyStored_of h2, keyStored_of h3, ?_⟩
  · split at h1
    · rename_i ci hf
      obtain ⟨hl, ht⟩ := of_decide_eq_true h1
      exact ⟨ci, _, hf, hl, ht⟩
    · cases h1
  · split at h4
    · rename_i cv pf hf; exact ⟨cv, pf, _, hf, of_decide_eq_true h4⟩
    · cases h4

theorem prodProjEntry_of {e : ProjEntry .anon} {kMk : KKey}
    (h : prodProjEntryB e kMk = true) :
    e.ctor = kMk ∧ e.numParams = 2 ∧ e.numFields = 2 ∧ ∀ ψ, Level.eval ψ e.structSort ≠ 0 := by
  simp only [prodProjEntryB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, b, c⟩ := of_decide_eq_true h1
  refine ⟨a, b, c, fun ψ => ?_⟩
  split at h2
  · rename_i l hl; rw [hl]; simp [Level.eval]
  · cases h2

theorem prodBasis_of_check {lk : LimbKeys} (h : prodBasisB env lk = true) : ProdBasis env lk := by
  simp only [prodBasisB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · split at h1
    · rename_i cv caps hf; exact ⟨cv, caps, hf, of_decide_eq_true h1⟩
    · cases h1
  · split at h2
    · rename_i cv hf; exact ⟨cv, hf, of_decide_eq_true h2⟩
    · cases h2
  · split at h3
    · rename_i e he
      obtain ⟨a, b, c, d⟩ := prodProjEntry_of h3
      exact ⟨e, he, a, b, c, d⟩
    · cases h3
  · split at h4
    · rename_i e he
      obtain ⟨a, b, c, d⟩ := prodProjEntry_of h4
      exact ⟨e, he, a, b, c, d⟩
    · cases h4

theorem limbStmt_of_check {tk : TowKeys} {lk : LimbKeys} {kc kThm : KKey} {op : LimbOp}
    (h : limbStmtB env tk lk kc kThm op = true) : LimbStmt env tk lk kc kThm op := by
  simp only [limbStmtB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨keyStored_of h1, keyStored_of h2,
    fun o ho => keyStored_of (List.all_eq_true.mp h3 o ho), ?_⟩
  split at h4
  · rename_i cv pf hf; exact ⟨cv, pf, _, hf, of_decide_eq_true h4⟩
  · cases h4

end CheckSound

end IxCC.Grounding
