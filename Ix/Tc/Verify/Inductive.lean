import Ix.Tc.Verify.Decl

/-!
# Ambient inductive oracle

Lean4Lean currently leaves both `VInductDecl.WF` and `VEnv.addInduct` as
opaque `sorry` definitions.  Requiring an equation involving that operation
here would make the ambient-inductive precondition impossible to instantiate
without adding another axiom.  G2 therefore records the semantic consequences
needed by the checker directly:

* every admitted concrete inductive-family constant has an exact raw Theory
  translation and lookup;
* its Theory constant is well-formed;
* the post-environment is well-formed and extends the prior environment;
* every concrete recursor rule has an explicit, well-formed Theory defeq
  witness headed by that recursor.

`InductiveOracle` is an explicit assumption boundary, not a claim that Ix's
inductive checker has already been verified.  The later inductive milestone
must construct this interface from block checking and a completed
Lean4Lean `addInduct` specification.  Keeping the interface in terms of
semantic consequences permits a closed Nat model with no new Lean axiom now,
while the recursor clause prevents future whnf proofs from treating
computation rules as an unrecorded ambient fact.
-/

namespace Ix.Tc

open Lean4Lean (VConstant VDefEq VEnv VExpr)

/-- Concrete declaration kinds admitted through an ambient inductive block.
Standalone declarations and quotients cannot cross this boundary. -/
def KConst.IsInductiveMember : KConst .anon → Prop
  | .indc .. | .ctor .. | .recr .. => True
  | _ => False

/-- Membership of a concrete rule in a recursor declaration. -/
def KConst.HasRecursorRule (c : KConst .anon) (rule : RecRule .anon) : Prop :=
  match c with
  | .recr (rules := rules) .. => rule ∈ rules
  | _ => False

/-- A Theory expression is an application spine headed by `name`. -/
inductive HeadConst (name : Lean.Name) : VExpr → Prop
  | const (levels : List Lean4Lean.VLevel) :
    HeadConst name (.const name levels)
  | app {fn arg : VExpr} : HeadConst name fn → HeadConst name (.app fn arg)

/-- Raw translation of one constant supplied by an ambient inductive block.
There is intentionally no block-typing derivation here; that semantic fact is
the oracle boundary. -/
structure RawInductiveConstRel (env : VEnv)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (id : KId .anon) (c : KConst .anon) (name : Lean.Name)
    (ci : VConstant) : Prop where
  kind : c.IsInductiveMember
  nameEq : nameOf id.addr = some name
  uvars : c.lvls.toNat = ci.uvars
  type : RawExprRel env nameOf trProj [] c.ty ci.type

namespace RawInductiveConstRel

theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {c : KConst .anon} {name : Lean.Name}
    {ci : VConstant}
    (h : RawInductiveConstRel env nameOf trProj id c name ci) :
    RawInductiveConstRel env' nameOf trProj id c name ci :=
  ⟨h.kind, h.nameEq, h.uvars, h.type.mono henv⟩

end RawInductiveConstRel

/-- Semantic evidence for one concrete recursor rule.  The registered Theory
defeq is well-formed, its left side is headed by the translated recursor, and
its right side is the raw translation of the concrete rule body.  K1 will
refine the exact argument-spine correspondence used by reduction. -/
def RawRecursorRuleRel (env : VEnv)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel)
    (id : KId .anon) (c : KConst .anon) (rule : RecRule .anon) : Prop :=
  ∃ name constant defeq,
    RawInductiveConstRel env nameOf trProj id c name constant ∧
    env.constants name = some constant ∧
    env.defeqs defeq ∧
    defeq.WF env ∧
    HeadConst name defeq.lhs ∧
    RawExprRel env nameOf trProj [] rule.rhs defeq.rhs

namespace RawRecursorRuleRel

theorem mono {env env' : VEnv} (henv : env ≤ env')
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {c : KConst .anon} {rule : RecRule .anon}
    (h : RawRecursorRuleRel env nameOf trProj id c rule) :
    RawRecursorRuleRel env' nameOf trProj id c rule := by
  obtain ⟨name, constant, defeq, hraw, hlookup, hregistered, hwf, hhead,
    hrhs⟩ := h
  exact ⟨name, constant, defeq, hraw.mono henv,
    henv.constants hlookup, henv.defeqs hregistered, hwf.mono henv, hhead,
    hrhs.mono henv⟩

end RawRecursorRuleRel

/-- One oracle-backed admission of an already-validated ambient inductive
block.  `members` is exact for this admission step; `fresh` prevents the
oracle from re-certifying an existing trusted id.

The oracle records `before ≤ after` rather than an opaque
`before.addInduct = some after` equation.  These are exactly the consequences
used before E2, and unlike the unfinished upstream operation they admit real
models. -/
structure InductiveOracle (trProj : RawProjRel) (catalog : Catalog)
    (nameOf : Address → Option Lean.Name) (trusted : KId .anon → Prop)
    (before : VEnv) where
  members : KId .anon → Prop
  nonempty : ∃ id, members id
  fresh : ∀ ⦃id⦄, members id → ¬trusted id
  after : VEnv
  envLE : before ≤ after
  blockWF : after.WF
  translateBlock : ∀ ⦃id⦄, members id →
    ∃ c name ci,
      catalog id = some c ∧
      RawInductiveConstRel after nameOf trProj id c name ci ∧
      after.constants name = some ci ∧
      ci.WF after
  recursorFacts : ∀ ⦃id c rule⦄,
    members id → catalog id = some c → c.HasRecursorRule rule →
      RawRecursorRuleRel after nameOf trProj id c rule

namespace InductiveOracle

/-- Add exactly this oracle block to the trusted predicate. -/
def TrustBlock {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv}
    (oracle : InductiveOracle trProj catalog nameOf trusted before) :
    KId .anon → Prop :=
  fun id => oracle.members id ∨ trusted id

theorem trust_member {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv} (oracle : InductiveOracle trProj catalog nameOf trusted before)
    {id : KId .anon} (h : oracle.members id) : oracle.TrustBlock id :=
  Or.inl h

theorem trust_old {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv} (oracle : InductiveOracle trProj catalog nameOf trusted before)
    {id : KId .anon} (h : trusted id) : oracle.TrustBlock id :=
  Or.inr h

theorem catalogued {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {before : VEnv} (oracle : InductiveOracle trProj catalog nameOf trusted before)
    {id : KId .anon} (h : oracle.members id) : Catalog.Contains catalog id := by
  obtain ⟨c, _, _, hcat, _⟩ := oracle.translateBlock h
  exact ⟨c, hcat⟩

end InductiveOracle

end Ix.Tc
