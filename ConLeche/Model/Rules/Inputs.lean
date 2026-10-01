module

public import ConLeche.Model.Rules.Motive

public section

/-!
# The environment-level inputs of the soundness (task #305)

What the soundness of a derivation reads about the ENVIRONMENT — the
stored data's readings, gradings and laws — and nothing about the
implementation.  One structure, `RulesInputs`, sorted by the tier that
discharges each field.

Seven fields are the laws `EnvModelM` already carries: `ConstType`,
`AcvalValid`, `NatHeads`, `AcvalDefnInst`, `TowerOk`, `RecRules` and
`CapsOk`, all of them `Model/Annot/Laws.lean`'s (re-exported by
`Model/Annot/EnvModelM.lean`).  `RulesInputs.ofEnvModelM` below reads
each of them off the fold's invariant.  No `Model/Steps/*` exists: the
tier was deleted at the task #305 closing, and the definitions that
used to be restated here are the originals.

Two fields are NEW SHAPES:

* `NatSuccRow` / `NatOpRow` — the literal accelerations' semantic
  content, stated at the shapes `reduceNat` fires on with the
  arguments already at literal readings (`rawNatLit?`), and with the
  subject's reading a premise.  They are proved in
  `Model/NatStep.lean` from `EnvModelM.nat_ops`/`div_mod`, which is
  where the content lives; they stay ARGUMENTS of `ofEnvModelM`
  because that file sits above this one (`Model/Capstone.lean`'s
  `RulesInputs.ofSem` supplies them).

The row for the `Red.natLit` step (`lit n ↦ natLitToConstructor n`)
needs no input: the reading is invisible to the step
(`denoteMeta_litToCtorIfNat`); the string expansion likewise
(`denotePStrLit_of_guard`).
-/
namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The successor packing's semantic row**: `Nat.succ w` at a literal
reading of `w` interprets as the packed literal, which reads and is
graded. -/
@[expose] def NatSuccRow {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {d : Nat} {w : Expr} {n : Nat} {Δa : List AnnotTerm} {ea : AnnotTerm},
    ConLeche.natLitSupported env = true →
    ConLeche.rawNatLit? w = some n →
    denoteMeta m.acval env φ d (.app (.const natSuccName []) w) = some ea →
    Graded V Δa ea →
    ∃ ra, denoteMeta m.acval env φ d (.lit (.natVal (n + 1))) = some ra ∧
      Graded V Δa ra ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ra

/-- **The binary acceleration's semantic row**: a stored operation on
two literal readings interprets as `natOpResult`, which reads and is
graded. -/
@[expose] def NatOpRow {env : Env} (m : EnvModel V env) (φ : Name → Nat) :
    Prop :=
  ∀ {d : Nat} {c : Name} {wa wb r : Expr} {n₁ n₂ : Nat} {Δa : List AnnotTerm}
    {ea : AnnotTerm},
    c ∈ natBinOpNames → ConLeche.natOpStored env c = true →
    ConLeche.rawNatLit? wa = some n₁ → ConLeche.rawNatLit? wb = some n₂ →
    ConLeche.natOpResult c n₁ n₂ = some r →
    denoteMeta m.acval env φ d (.app (.app (.const c []) wa) wb) = some ea →
    Graded V Δa ea →
    ∃ ra, denoteMeta m.acval env φ d r = some ra ∧
      Graded V Δa ra ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ra

/-- **The environment-level inputs of the rules soundness**, at one
`(env, m, φ)`, sorted by discharging tier. -/
structure RulesInputs (V : Type w) [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop where
  /-- install tier: a stored constant's type row -/
  const_ty : ConstType m φ
  /-- install tier: leaf bit-validity -/
  leaf_valid : AcvalValid m
  /-- install tier: the numeral heads -/
  nat_heads : NatHeads m φ
  /-- install tier: a stored definition's value reads to its leaf -/
  defn : AcvalDefnInst m
  /-- install tier: the projection tables' laws -/
  tower_ok : TowerOk m φ
  /-- iota tier: the stored recursors' fired contracts -/
  rec_rules : RecRules m φ
  /-- caps tier: the stored families' capability laws -/
  caps_ok : CapsOk m
  /-- literal tier: successor packing -/
  nat_succ : NatSuccRow m φ
  /-- literal tier: the binary operations -/
  nat_op : NatOpRow m φ

/-- **The env-tier inputs, from the fold's invariant**: every field but
the two literal rows is an `EnvModelM` projection; the rows stay
arguments because `natSuccRow_of`/`natOpRow_of` (`Model/NatStep.lean`)
sit above this file — `Model/Capstone.lean`'s `RulesInputs.ofSem`
supplies them.  Replaces `TierInputsAt.ofEnvModelM` (task #305
closing). -/
theorem RulesInputs.ofEnvModelM {env : Env} {φ : Name → Nat}
    (mp : EnvModelM V μ env)
    (hsucc : NatSuccRow mp.base2 φ) (hop : NatOpRow mp.base2 φ) :
    RulesInputs V mp.base2 φ where
  const_ty := mp.constType
  leaf_valid := mp.acvalValid
  nat_heads := mp.nat_heads φ
  defn := mp.defn_reads
  tower_ok := mp.tower_ok φ
  rec_rules := mp.rec_rules φ
  caps_ok := mp.caps_ok
  nat_succ := hsucc
  nat_op := hop

end ConLeche.Model.Rules
