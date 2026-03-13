/-
  Ix.Theory.Env: Specification-level environment and declarations.

  Mirrors Ix.Kernel.Types (ConstantInfo, RecursorRule, QuotKind) but
  simplified for metatheory: no metadata, no isUnsafe, no hints.
  Uses Nat constant IDs and TExpr (= SExpr SLevel).
-/
import Ix.Theory.Expr

namespace Ix.Theory

/-! ## Enums -/

/-- Quotient constant kinds. Mirrors Ix.Kernel.Types.QuotKind. -/
inductive SQuotKind where
  | type | ctor | lift | ind
  deriving Inhabited, BEq, DecidableEq

/-! ## Recursor rules -/

/-- A single recursor computation rule. Mirrors Ix.Kernel.Types.RecursorRule. -/
structure SRecursorRule where
  ctor    : Nat      -- constructor constant ID
  nfields : Nat
  rhs     : TExpr

/-! ## SConstantInfo -/

/-- Constant declarations, mirroring Ix.Kernel.Types.ConstantInfo.
    Each variant carries the typing-relevant fields from the corresponding
    Kernel structure. Metadata (names, binder info) and implementation
    details (hints, safety, isUnsafe) are dropped. -/
inductive SConstantInfo where
  | axiom   (uvars : Nat) (type : TExpr)
  | defn    (uvars : Nat) (type : TExpr) (value : TExpr)
            (all : List Nat)
  | theorem (uvars : Nat) (type : TExpr) (value : TExpr)
            (all : List Nat)
  | opaque  (uvars : Nat) (type : TExpr) (value : TExpr)
            (all : List Nat)
  | quot    (uvars : Nat) (type : TExpr) (kind : SQuotKind)
  | induct  (uvars : Nat) (type : TExpr)
            (numParams numIndices : Nat) (all ctors : List Nat)
            (isRec isReflexive : Bool)
  | ctor    (uvars : Nat) (type : TExpr) (induct : Nat)
            (cidx numParams numFields : Nat)
  | recursor (uvars : Nat) (type : TExpr) (all : List Nat)
             (numParams numIndices numMotives numMinors : Nat)
             (rules : List SRecursorRule) (k : Bool)

namespace SConstantInfo

/-- Number of universe parameters. -/
def uvars : SConstantInfo → Nat
  | .axiom u .. | .defn u .. | .theorem u .. | .opaque u ..
  | .quot u .. | .induct u .. | .ctor u .. | .recursor u .. => u

/-- The type of this constant. -/
def type : SConstantInfo → TExpr
  | .axiom _ t | .defn _ t .. | .theorem _ t .. | .opaque _ t ..
  | .quot _ t .. | .induct _ t .. | .ctor _ t .. | .recursor _ t .. => t

/-- The value (body) of a definition, theorem, or opaque, if present. -/
def value? : SConstantInfo → Option TExpr
  | .defn _ _ v .. | .theorem _ _ v .. | .opaque _ _ v .. => some v
  | _ => none

end SConstantInfo

/-! ## Definitional equality axioms -/

/-- A definitional equality axiom (delta, iota, quot reduction, etc.).
    Used by the `extra` constructor in the typing judgment. -/
structure SDefEq where
  uvars : Nat
  lhs   : TExpr
  rhs   : TExpr
  type  : TExpr

/-! ## Environment -/

/-- The specification environment: constants by numeric ID, defeqs as a predicate.
    Functional representation following lean4lean's VEnv. -/
@[ext] structure SEnv where
  constants : Nat → Option SConstantInfo
  defeqs    : SDefEq → Prop

/-- The empty environment. -/
def SEnv.empty : SEnv := ⟨fun _ => none, fun _ => False⟩

instance : EmptyCollection SEnv := ⟨SEnv.empty⟩

/-- Add a constant, failing if the ID is already taken. -/
def SEnv.addConst (env : SEnv) (id : Nat) (ci : SConstantInfo) : Option SEnv :=
  match env.constants id with
  | some _ => none
  | none => some { env with
      constants := fun n => if id = n then some ci else env.constants n }

/-- Add a definitional equality axiom (always succeeds). -/
def SEnv.addDefEq (env : SEnv) (df : SDefEq) : SEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

/-! ## Monotonicity -/

/-- `env₁ ≤ env₂` means env₂ extends env₁: all constants and defeqs are preserved. -/
structure SEnv.LE (env₁ env₂ : SEnv) : Prop where
  constants : env₁.constants n = some a → env₂.constants n = some a
  defeqs    : env₁.defeqs df → env₂.defeqs df

instance : LE SEnv := ⟨SEnv.LE⟩

theorem SEnv.LE.rfl {env : SEnv} : env ≤ env :=
  ⟨id, id⟩

theorem SEnv.LE.trans {a b c : SEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.constants ∘ h1.constants, h2.defeqs ∘ h1.defeqs⟩

theorem SEnv.addConst_le {env env' : SEnv} {c : Nat} {ci : SConstantInfo}
    (h : env.addConst c ci = some env') : env ≤ env' := by
  unfold addConst at h
  split at h <;> simp at h
  subst h
  constructor
  · intro n a hc
    simp only
    split
    · next he => subst he; simp [hc] at *
    · exact hc
  · intro df hd; exact hd

theorem SEnv.addConst_self {env env' : SEnv} {c : Nat} {ci : SConstantInfo}
    (h : env.addConst c ci = some env') : env'.constants c = some ci := by
  unfold addConst at h
  split at h <;> simp at h
  subst h; simp

theorem SEnv.addDefEq_le {env : SEnv} {df : SDefEq} : env ≤ env.addDefEq df :=
  ⟨id, fun h => Or.inr h⟩

theorem SEnv.addDefEq_self {env : SEnv} {df : SDefEq} : (env.addDefEq df).defeqs df :=
  Or.inl rfl

end Ix.Theory
