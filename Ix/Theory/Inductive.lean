/-
  Ix.Theory.Inductive: Well-formed inductive declarations and reduction rules.

  Generalizes the Nat formalization pattern (`WFNatEnv`) to arbitrary single
  non-mutual inductives. Defines:
  - Expression helpers (`mkApps`) with closedness lemmas
  - Iota rule construction (recursor on constructor → rule RHS)
  - K-rule construction (Prop inductive with single zero-field constructor)
  - Projection rule construction (structure field extraction)
  - `WFInductive` predicate asserting all constants and reduction rules exist

  All reduction rules are encoded as `SDefEq` entries for the `extra` rule in
  the typing judgment. Arguments are universally quantified over closed expressions
  to ensure compatibility with `WFClosed`.

  Reference: docs/theory/kernel.md Part IX (reduction strategies).
-/
import Ix.Theory.Env

namespace Ix.Theory

open SExpr

variable {L : Type}

/-! ## Expression helpers -/

/-- Apply a function to a list of arguments left-to-right:
    `mkApps f [a, b, c] = app (app (app f a) b) c`. -/
def mkApps (f : SExpr L) : List (SExpr L) → SExpr L
  | [] => f
  | a :: as => mkApps (.app f a) as

@[simp] theorem mkApps_nil (f : SExpr L) : mkApps f [] = f := rfl
@[simp] theorem mkApps_cons (f : SExpr L) (a : SExpr L) (as : List (SExpr L)) :
    mkApps f (a :: as) = mkApps (.app f a) as := rfl

theorem mkApps_append (f : SExpr L) (as bs : List (SExpr L)) :
    mkApps f (as ++ bs) = mkApps (mkApps f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

theorem mkApps_closedN {f : SExpr L} {args : List (SExpr L)} {k : Nat}
    (hf : ClosedN f k) (ha : ∀ a ∈ args, ClosedN a k) :
    ClosedN (mkApps f args) k := by
  induction args generalizing f with
  | nil => exact hf
  | cons a as ih =>
    exact ih ⟨hf, ha a (.head _)⟩ fun a h => ha a (.tail _ h)

theorem mkApps_closed {f : SExpr L} {args : List (SExpr L)}
    (hf : Closed f) (ha : ∀ a ∈ args, Closed a) :
    Closed (mkApps f args) := mkApps_closedN hf ha

theorem const_closed (c : Nat) (ls : List L) : Closed (.const c ls : SExpr L) := trivial

/-! ## instL interaction with mkApps -/

theorem mkApps_instL (ls : List SLevel) (f : TExpr) (args : List TExpr) :
    (mkApps f args).instL ls = mkApps (f.instL ls) (args.map (·.instL ls)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [mkApps_cons, List.map_cons]; rw [ih]; rfl

/-! ## Closedness for expression lists -/

/-- All expressions in a list are closed. -/
def AllClosed (es : List TExpr) : Prop := ∀ a ∈ es, Closed a

theorem AllClosed.nil : AllClosed [] := fun _ h => nomatch h

theorem AllClosed.cons (ha : Closed a) (has : AllClosed as) : AllClosed (a :: as) :=
  fun x hx => by cases hx with | head => exact ha | tail _ h => exact has x h

theorem AllClosed.append (ha : AllClosed as) (hb : AllClosed bs) : AllClosed (as ++ bs) :=
  fun x hx => by
    cases List.mem_append.mp hx with
    | inl h => exact ha x h
    | inr h => exact hb x h

theorem AllClosed.singleton (ha : Closed a) : AllClosed [a] := AllClosed.cons ha AllClosed.nil

theorem AllClosed.of_subset {as bs : List TExpr} (h : ∀ a ∈ as, a ∈ bs)
    (hbs : AllClosed bs) : AllClosed as :=
  fun a ha => hbs a (h a ha)

/-! ## Iota rule construction

    For constructor `cᵢ` with `nfields` fields, the iota reduction is:
    ```
    rec.{ls} params motive minors indices (cᵢ.{ls} params fields)
    ≡ ruleᵢ.instL(ls) params motive minors fields
    : motive indices (cᵢ.{ls} params fields)
    ```
    Since `numMotives = 1` (non-mutual), the motive is a single expression. -/

/-- LHS of iota rule:
    `rec.{ls} params motive minors indices (ctor.{ls} params fields)` -/
def mkIotaLHS (recId ctorId : Nat) (ls : List SLevel)
    (params : List TExpr) (motive : TExpr) (minors indices fields : List TExpr) : TExpr :=
  mkApps (.const recId ls)
    (params ++ [motive] ++ minors ++ indices ++
      [mkApps (.const ctorId ls) (params ++ fields)])

/-- RHS of iota rule:
    `ruleRhs.instL(ls) params motive minors fields` -/
def mkIotaRHS (ruleRhs : TExpr) (ls : List SLevel)
    (params : List TExpr) (motive : TExpr) (minors fields : List TExpr) : TExpr :=
  mkApps (ruleRhs.instL ls) (params ++ [motive] ++ minors ++ fields)

/-- Type of iota rule:
    `motive indices (ctor.{ls} params fields)` -/
def mkIotaType (motive : TExpr) (ctorId : Nat) (ls : List SLevel)
    (params indices fields : List TExpr) : TExpr :=
  mkApps motive (indices ++ [mkApps (.const ctorId ls) (params ++ fields)])

/-- Assemble the full iota SDefEq. Universe levels are pre-instantiated (uvars = 0). -/
def mkIotaRule (recId ctorId : Nat) (ruleRhs : TExpr) (ls : List SLevel)
    (params : List TExpr) (motive : TExpr) (minors indices fields : List TExpr) : SDefEq :=
  { uvars := 0,
    lhs := mkIotaLHS recId ctorId ls params motive minors indices fields,
    rhs := mkIotaRHS ruleRhs ls params motive minors fields,
    type := mkIotaType motive ctorId ls params indices fields }

/-! ### Iota closedness -/

theorem mkIotaLHS_closed {recId ctorId : Nat} {ls : List SLevel}
    {params : List TExpr} {motive : TExpr} {minors indices fields : List TExpr}
    (hp : AllClosed params) (hmo : Closed motive) (hmi : AllClosed minors)
    (hix : AllClosed indices) (hf : AllClosed fields) :
    (mkIotaLHS recId ctorId ls params motive minors indices fields).Closed := by
  unfold mkIotaLHS
  apply mkApps_closed (const_closed _ _)
  -- ((((params ++ [motive]) ++ minors) ++ indices) ++ [ctor_app])
  exact AllClosed.append
    (AllClosed.append
      (AllClosed.append
        (AllClosed.append hp (AllClosed.singleton hmo))
        hmi)
      hix)
    (AllClosed.singleton (mkApps_closed (const_closed _ _) (AllClosed.append hp hf)))

theorem mkIotaRHS_closed {ruleRhs : TExpr} {ls : List SLevel}
    {params : List TExpr} {motive : TExpr} {minors fields : List TExpr}
    (hr : ruleRhs.Closed) (hp : AllClosed params) (hmo : Closed motive)
    (hmi : AllClosed minors) (hf : AllClosed fields) :
    (mkIotaRHS ruleRhs ls params motive minors fields).Closed := by
  unfold mkIotaRHS
  -- (((params ++ [motive]) ++ minors) ++ fields)
  exact mkApps_closed (ClosedN.instL hr _)
    (AllClosed.append
      (AllClosed.append
        (AllClosed.append hp (AllClosed.singleton hmo))
        hmi)
      hf)

theorem mkIotaType_closed {motive : TExpr} {ctorId : Nat} {ls : List SLevel}
    {params indices fields : List TExpr}
    (hmo : Closed motive) (hp : AllClosed params) (hix : AllClosed indices)
    (hf : AllClosed fields) :
    (mkIotaType motive ctorId ls params indices fields).Closed := by
  unfold mkIotaType
  exact mkApps_closed hmo
    (AllClosed.append hix (AllClosed.singleton (mkApps_closed (const_closed _ _) (AllClosed.append hp hf))))

theorem mkIotaRule_closed {recId ctorId : Nat} {ruleRhs : TExpr} {ls : List SLevel}
    {params : List TExpr} {motive : TExpr} {minors indices fields : List TExpr}
    (hr : ruleRhs.Closed) (hmo : Closed motive)
    (hp : AllClosed params) (hmi : AllClosed minors) (hix : AllClosed indices)
    (hf : AllClosed fields) :
    let r := mkIotaRule recId ctorId ruleRhs ls params motive minors indices fields
    r.lhs.Closed ∧ r.rhs.Closed ∧ r.type.Closed :=
  ⟨mkIotaLHS_closed hp hmo hmi hix hf,
   mkIotaRHS_closed hr hp hmo hmi hf,
   mkIotaType_closed hmo hp hix hf⟩

/-! ## K-rule construction

    For Prop inductives with a single zero-field constructor, K-reduction
    returns the minor premise without inspecting the major:
    ```
    rec.{ls} params motive minor indices major ≡ minor
    : motive indices major
    ``` -/

/-- Assemble the K-reduction SDefEq. -/
def mkKRule (recId : Nat) (ls : List SLevel)
    (params : List TExpr) (motive minor : TExpr)
    (indices : List TExpr) (major : TExpr) : SDefEq :=
  { uvars := 0,
    lhs := mkApps (.const recId ls)
      (params ++ [motive, minor] ++ indices ++ [major]),
    rhs := minor,
    type := mkApps motive (indices ++ [major]) }

theorem mkKRule_closed {recId : Nat} {ls : List SLevel}
    {params : List TExpr} {motive minor : TExpr}
    {indices : List TExpr} {major : TExpr}
    (hp : AllClosed params) (hmo : Closed motive)
    (hmi : Closed minor) (hix : AllClosed indices) (hmaj : Closed major) :
    let r := mkKRule recId ls params motive minor indices major
    r.lhs.Closed ∧ r.rhs.Closed ∧ r.type.Closed := by
  refine ⟨?_, hmi, ?_⟩
  · -- (((params ++ [motive, minor]) ++ indices) ++ [major])
    exact mkApps_closed (const_closed _ _)
      (AllClosed.append
        (AllClosed.append
          (AllClosed.append hp (AllClosed.cons hmo (AllClosed.cons hmi AllClosed.nil)))
          hix)
        (AllClosed.singleton hmaj))
  · exact mkApps_closed hmo (AllClosed.append hix (AllClosed.singleton hmaj))

/-! ## Projection rule construction

    For structures (single-constructor, 0 indices, non-recursive):
    ```
    proj typeName i (ctor.{ls} params fields) ≡ fields[i]
    : fieldType
    ```
    The `fieldType` is given externally (computed from the constructor type). -/

/-- Assemble the projection reduction SDefEq. -/
def mkProjRule (typeName ctorId : Nat) (fieldIdx : Nat) (ls : List SLevel)
    (params fields : List TExpr) (fieldType : TExpr)
    (hf : fieldIdx < fields.length) : SDefEq :=
  { uvars := 0,
    lhs := .proj typeName fieldIdx (mkApps (.const ctorId ls) (params ++ fields)),
    rhs := fields[fieldIdx],
    type := fieldType }

theorem mkProjRule_closed {typeName ctorId : Nat} {fieldIdx : Nat} {ls : List SLevel}
    {params fields : List TExpr} {fieldType : TExpr}
    {hf : fieldIdx < fields.length}
    (hp : AllClosed params) (hfl : AllClosed fields) (ht : Closed fieldType) :
    let r := mkProjRule typeName ctorId fieldIdx ls params fields fieldType hf
    r.lhs.Closed ∧ r.rhs.Closed ∧ r.type.Closed :=
  ⟨mkApps_closed (const_closed _ _) (AllClosed.append hp hfl),
   hfl _ (List.getElem_mem hf),
   ht⟩

/-! ## WFInductive: well-formed inductive declaration

    Asserts that the environment contains all constants and reduction rules
    for a single non-mutual inductive type. Generalizes `WFNatEnv`.

    Since this is non-mutual, `numMotives = 1` and the motive is a single
    expression (not a list). -/

/-- Well-formed inductive declaration in the specification environment. -/
structure WFInductive (env : SEnv) where
  -- Identifiers
  indId : Nat
  ctorIds : List Nat
  recId : Nat
  -- Inductive metadata
  uvars : Nat
  indType : TExpr
  numParams : Nat
  numIndices : Nat
  all : List Nat
  isRec : Bool
  isReflexive : Bool
  -- Recursor metadata
  recType : TExpr
  numMinors : Nat
  rules : List SRecursorRule
  k : Bool
  -- Consistency (placed before has* fields so they're in scope)
  numMinors_eq : numMinors = ctorIds.length
  rules_len : rules.length = ctorIds.length
  indType_closed : indType.Closed
  recType_closed : recType.Closed
  rules_rhs_closed : ∀ r ∈ rules, r.rhs.Closed
  -- The inductive constant exists in the environment
  hasInduct : env.constants indId = some
    (.induct uvars indType numParams numIndices all ctorIds isRec isReflexive)
  -- Each constructor exists with the correct metadata
  hasCtors : ∀ i (hi : i < ctorIds.length),
    ∃ ctorType nfields,
    env.constants (ctorIds[i]) = some
      (.ctor uvars ctorType indId i numParams nfields) ∧
    ctorType.Closed
  -- The recursor constant exists
  hasRec : env.constants recId = some
    (.recursor uvars recType all numParams numIndices 1 numMinors rules k)
  -- Iota reduction: for each constructor, the reduction rule exists
  -- for all closed argument tuples of the right lengths.
  -- Since numMotives = 1, the motive is a single expression.
  hasIota : ∀ i (hi : i < ctorIds.length),
    ∀ (ls : List SLevel) (params : List TExpr) (motive : TExpr)
      (minors indices fields : List TExpr),
    ls.length = uvars →
    params.length = numParams →
    minors.length = numMinors →
    indices.length = numIndices →
    fields.length = (rules[i]'(rules_len.symm ▸ hi)).nfields →
    AllClosed params → motive.Closed → AllClosed minors →
    AllClosed indices → AllClosed fields →
    env.defeqs (mkIotaRule recId (ctorIds[i])
      (rules[i]'(rules_len.symm ▸ hi)).rhs ls params motive minors indices fields)
  -- K-reduction: when `k = true`, the minor premise is returned directly
  hasK : k = true →
    ∀ (ls : List SLevel) (params : List TExpr) (motive minor : TExpr)
      (indices : List TExpr) (major : TExpr),
    ls.length = uvars →
    params.length = numParams →
    indices.length = numIndices →
    AllClosed params → motive.Closed → minor.Closed →
    AllClosed indices → major.Closed →
    env.defeqs (mkKRule recId ls params motive minor indices major)

/-! ### WFClosed compatibility -/

/-- Every iota defeq from a `WFInductive` has closed lhs/rhs/type. -/
theorem WFInductive.iota_defeq_closed (wfi : WFInductive env)
    {i : Nat} (hi : i < wfi.ctorIds.length)
    {ls : List SLevel} {params : List TExpr} {motive : TExpr}
    {minors indices fields : List TExpr}
    (hp : AllClosed params) (hmo : Closed motive) (hmi : AllClosed minors)
    (hix : AllClosed indices) (hf : AllClosed fields) :
    let r := mkIotaRule wfi.recId (wfi.ctorIds[i])
      (wfi.rules[i]'(wfi.rules_len.symm ▸ hi)).rhs ls params motive minors indices fields
    r.lhs.Closed ∧ r.rhs.Closed ∧ r.type.Closed :=
  mkIotaRule_closed
    (wfi.rules_rhs_closed _ (List.getElem_mem (wfi.rules_len.symm ▸ hi)))
    hmo hp hmi hix hf

/-- Every K-rule defeq from a `WFInductive` has closed lhs/rhs/type. -/
theorem WFInductive.k_defeq_closed (_wfi : WFInductive env)
    {ls : List SLevel} {params : List TExpr} {motive minor : TExpr}
    {indices : List TExpr} {major : TExpr}
    (hp : AllClosed params) (hmo : Closed motive)
    (hmi : Closed minor) (hix : AllClosed indices) (hmaj : Closed major) :
    let r := mkKRule _wfi.recId ls params motive minor indices major
    r.lhs.Closed ∧ r.rhs.Closed ∧ r.type.Closed :=
  mkKRule_closed hp hmo hmi hix hmaj

/-! ### Projection support for structures -/

/-- A structure is a single-constructor, zero-index, non-recursive inductive. -/
structure WFInductive.IsStruct (wfi : WFInductive env) : Prop where
  singleCtor : wfi.ctorIds.length = 1
  zeroIndices : wfi.numIndices = 0
  notRec : wfi.isRec = false

/-- Well-formed projection rules for a structure. -/
structure WFProjection (env : SEnv) (wfi : WFInductive env) where
  isStruct : wfi.IsStruct
  nfields : Nat
  hasProj : ∀ (fieldIdx : Nat) (hfi : fieldIdx < nfields),
    ∀ (ls : List SLevel) (params fields : List TExpr) (fieldType : TExpr),
    ls.length = wfi.uvars →
    params.length = wfi.numParams →
    (hfl : fields.length = nfields) →
    AllClosed params → AllClosed fields → Closed fieldType →
    env.defeqs (mkProjRule wfi.indId
      (wfi.ctorIds[0]'(by rw [isStruct.singleCtor]; omega))
      fieldIdx ls params fields fieldType (hfl ▸ hfi))

/-! ## Sanity checks -/

-- mkApps builds the expected application chain
#guard mkApps (.const 0 [] : SExpr Nat) [.lit 1, .lit 2] ==
    .app (.app (.const 0 []) (.lit 1)) (.lit 2)

-- mkApps on empty list is identity
#guard mkApps (.const 0 [] : SExpr Nat) [] == .const 0 []

-- mkIotaLHS for Nat.rec on Nat.zero (0 params, 1 motive, 2 minors, 0 indices, 0 fields)
-- Nat.rec motive z s Nat.zero
#guard (mkIotaLHS 3 1 ([] : List SLevel)
    [] (.const 99 []) [.const 98 [], .const 97 []] [] [] : TExpr) ==
    .app (.app (.app (.app (.const 3 []) (.const 99 [])) (.const 98 [])) (.const 97 []))
      (.const 1 [])

-- mkKRule: rec params motive minor major ≡ minor
#guard (mkKRule 5 ([] : List SLevel) [] (.const 10 []) (.const 20 []) [] (.const 30 []) : SDefEq).rhs ==
    .const 20 []

-- Projection rule: proj 0 2 (ctor [f0, f1, f2]) ≡ f2
#guard (mkProjRule 0 1 2 ([] : List SLevel)
    [] [.const 10 [], .const 20 [], .const 30 []] (.const 40 [])
    (by decide) : SDefEq).rhs == .const 30 []

end Ix.Theory
