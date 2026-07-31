import Ix.Tc.Verify.Whnf.Iota.NatRecognizer

/-!
# Constructive Nat-iota pattern matching

NatRecognizer identifies the exact recursor rule and the literal-major position used
by the linear Nat recognizer.  This slice crosses the next semantic boundary:
it constructs Lean4Lean's dependent `Pattern.Matches` capture map from exact
constant-spine shapes.

The bridge deliberately ends at the application through the major argument.
Any trailing application suffix must be split and typed before these matches
can be used to justify the production fast path; silently matching a prefix
as though it were the whole source would lose over-application semantics.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace HeadConstN

/-- Every exact constant-headed spine constructively matches the corresponding
`varN` pattern.  The existential capture map is produced by Lean4Lean's own
`Pattern.Matches.var` constructor at each application. -/
theorem matches_varN
    {name : Lean.Name} {arity : Nat} {source : VExpr}
    (h : HeadConstN name arity source) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : ((Lean4Lean.Pattern.const name).varN arity).Path → VExpr),
      Lean4Lean.Pattern.Matches
        ((Lean4Lean.Pattern.const name).varN arity)
        source levels captures := by
  induction h with
  | const levels =>
      exact ⟨levels, nofun, .const⟩
  | @app arity fn arg hprefix ih =>
      obtain ⟨levels, captures, hmatch⟩ := ih
      refine ⟨levels,
        (fun path : Option (((Lean4Lean.Pattern.const name).varN arity).Path) =>
          path.elim arg captures), ?_⟩
      simpa only [Lean4Lean.Pattern.varN, Nat.add_comm] using
        (Lean4Lean.Pattern.Matches.var (a' := arg) hmatch)

/-- The canonical Theory numeral zero is a nullary `Nat.zero` spine. -/
theorem natLit_zero :
    HeadConstN ``Nat.zero 0 (VExpr.natLit 0) := by
  exact .const []

/-- Every positive canonical Theory numeral is a unary `Nat.succ` spine;
the predecessor remains the single captured constructor argument. -/
theorem natLit_succ (predecessor : Nat) :
    HeadConstN ``Nat.succ 1 (VExpr.natLit (predecessor + 1)) := by
  change HeadConstN ``Nat.succ 1
    (.app (.const ``Nat.succ []) (VExpr.natLit predecessor))
  simpa using HeadConstN.app (HeadConstN.const (name := ``Nat.succ) [])

end HeadConstN

namespace RecursorIotaPattern

/-- Exact recursor and constructor spines construct the dependent match for
Lean4Lean's ordinary iota pattern.  The recursor levels and both capture maps
are exactly those built by `Pattern.Matches`; no choice principle is needed. -/
theorem matches_of_shapes
    {recursorName constructorName : Lean.Name}
    {majorIdx constructorArgs : Nat}
    {recursorPrefix major : VExpr}
    (hrecursor : HeadConstN recursorName majorIdx recursorPrefix)
    (hconstructor : HeadConstN constructorName constructorArgs major) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern recursorName majorIdx
          constructorName constructorArgs).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern recursorName majorIdx constructorName
          constructorArgs)
        (.app recursorPrefix major) levels captures := by
  obtain ⟨recursorLevels, recursorCaptures, hrecursorMatch⟩ :=
    hrecursor.matches_varN
  obtain ⟨_, constructorCaptures, hconstructorMatch⟩ :=
    hconstructor.matches_varN
  refine ⟨recursorLevels, Sum.elim recursorCaptures constructorCaptures, ?_⟩
  simpa only [RecursorIotaPattern, Lean4Lean.SimplePattern.toPattern] using
    Lean4Lean.Pattern.Matches.app hrecursorMatch hconstructorMatch

/-- Constructive matching and the counted-spine view are equivalent.  This
packages the registered-rule inversion together with the capture-map
construction and exposes the exact through-major boundary in either
direction. -/
theorem exists_matches_iff_shapes
    {recursorName constructorName : Lean.Name}
    {majorIdx constructorArgs : Nat} {source : VExpr} :
    (∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern recursorName majorIdx
          constructorName constructorArgs).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern recursorName majorIdx constructorName
          constructorArgs)
        source levels captures) ↔
      ∃ recursorPrefix major,
        source = .app recursorPrefix major ∧
        HeadConstN recursorName majorIdx recursorPrefix ∧
        HeadConstN constructorName constructorArgs major := by
  constructor
  · rintro ⟨_, _, hmatch⟩
    exact matches_shape hmatch
  · rintro ⟨recursorPrefix, major, rfl, hrecursor, hconstructor⟩
    exact matches_of_shapes hrecursor hconstructor

/-- A nullary zero major yields a concrete iota match. -/
theorem matches_natZero
    {recursorName : Lean.Name} {majorIdx : Nat}
    {recursorPrefix : VExpr}
    (hrecursor : HeadConstN recursorName majorIdx recursorPrefix) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern recursorName majorIdx
          ``Nat.zero 0).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern recursorName majorIdx ``Nat.zero 0)
        (.app recursorPrefix (VExpr.natLit 0)) levels captures :=
  matches_of_shapes hrecursor HeadConstN.natLit_zero

/-- A unary successor major yields a concrete iota match whose constructor
capture is the canonical predecessor numeral. -/
theorem matches_natSucc
    {recursorName : Lean.Name} {majorIdx predecessor : Nat}
    {recursorPrefix : VExpr}
    (hrecursor : HeadConstN recursorName majorIdx recursorPrefix) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern recursorName majorIdx
          ``Nat.succ 1).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern recursorName majorIdx ``Nat.succ 1)
        (.app recursorPrefix (VExpr.natLit (predecessor + 1)))
        levels captures :=
  matches_of_shapes hrecursor (HeadConstN.natLit_succ predecessor)

end RecursorIotaPattern

/-- The two constructor shapes that a trusted linear `Nat.rec` rule may use.
Rule position, constructor identity, constructor parameters, and fields are
all explicit: none is inferred merely from the literal value. -/
def NatRecIotaCase (pattern : RecursorRulePattern) (major : Nat) : Prop :=
  (major = 0 ∧
      pattern.ruleIndex = 0 ∧
      pattern.constructorName = ``Nat.zero ∧
      pattern.constructorParams = 0 ∧
      pattern.constructorFields = 0) ∨
    ∃ predecessor,
      major = predecessor + 1 ∧
      pattern.ruleIndex = 1 ∧
      pattern.constructorName = ``Nat.succ ∧
      pattern.constructorParams = 0 ∧
      pattern.constructorFields = 1

namespace NatRecIotaCase

/-- A certified Nat rule case gives the exact constructor-headed shape of
the canonical Theory numeral inspected by the fast path. -/
theorem major_shape
    {pattern : RecursorRulePattern} {major : Nat}
    (h : NatRecIotaCase pattern major) :
    HeadConstN pattern.constructorName
      (pattern.constructorParams.toNat + pattern.constructorFields.toNat)
      (VExpr.natLit major) := by
  rcases h with hzero | hsucc
  · rcases hzero with ⟨rfl, _, hname, hparams, hfields⟩
    simpa [hname, hparams, hfields] using HeadConstN.natLit_zero
  · obtain ⟨predecessor, rfl, _, hname, hparams, hfields⟩ := hsucc
    simpa [hname, hparams, hfields] using
      HeadConstN.natLit_succ predecessor

end NatRecIotaCase

namespace RecursorRulePattern

/-- Once the recursor prefix and Nat constructor case are fixed, the exact
trusted rule pattern has a concrete Lean4Lean match and capture map. -/
theorem matches_natLiteral
    {pattern : RecursorRulePattern} {major : Nat}
    {recursorPrefix : VExpr}
    (hrecursor : HeadConstN pattern.recursorName pattern.majorIdx
      recursorPrefix)
    (hcase : NatRecIotaCase pattern major) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern pattern.recursorName
          pattern.majorIdx pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat)).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern pattern.recursorName pattern.majorIdx
          pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat))
        (.app recursorPrefix (VExpr.natLit major)) levels captures :=
  RecursorIotaPattern.matches_of_shapes hrecursor hcase.major_shape

end RecursorRulePattern

namespace RecM
namespace TrAppSpine

/-- A translated concrete spine whose head is a named constant becomes an
exactly counted Theory constant spine.  In particular, this theorem does not
forget how many arguments precede a descriptor-selected major. -/
theorem headConstN
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : List (KExpr .anon)} {resultV : VExpr} {name : Lean.Name}
    (h : TrAppSpine env uvars nameOf trProj Delta
      (.const id us info) args resultV)
    (hname : nameOf id.addr = some name) :
    HeadConstN name args.length resultV := by
  induction h with
  | head hhead =>
      cases hhead with
      | const translatedName _ _ _ =>
          have hnames : _ = name :=
            Option.some.inj (translatedName.symm.trans hname)
          subst name
          exact .const _
  | app hprefix _ _ _ ih =>
      simpa using HeadConstN.app ih

/-- Translation of precisely the arguments before the major supplies the
recursor half of the selected pattern match.  The length equality is an
explicit prefix-boundary obligation. -/
theorem matches_natRecRulePrefix
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : List (KExpr .anon)} {recursorPrefix : VExpr}
    {pattern : RecursorRulePattern} {major : Nat}
    (hspine : TrAppSpine env uvars nameOf trProj Delta
      (.const id us info) args recursorPrefix)
    (hname : nameOf id.addr = some pattern.recursorName)
    (hlength : args.length = pattern.majorIdx)
    (hcase : NatRecIotaCase pattern major) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern pattern.recursorName
          pattern.majorIdx pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat)).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern pattern.recursorName pattern.majorIdx
          pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat))
        (.app recursorPrefix (VExpr.natLit major)) levels captures := by
  apply pattern.matches_natLiteral
  · simpa only [hlength] using hspine.headConstN hname
  · exact hcase

end TrAppSpine
end RecM

namespace RawRecursorRulePatternRel

/-- The translation bridge can take its recursor name directly from trusted
pattern provenance.  Constructor shape remains a separate Nat-specific fact,
so a catalogued rule at index zero or one is not silently assumed to be the
corresponding Nat rule. -/
theorem matches_natLiteralPrefix
    {env : Lean4Lean.VEnv} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {id : KId .anon} {recursor : KConst .anon} {rule : RecRule .anon}
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel env catalog nameOf id recursor
      rule pattern)
    {uvars : Nat} {Delta : KVLCtx}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : List (KExpr .anon)} {recursorPrefix : VExpr} {major : Nat}
    (hspine : RecM.TrAppSpine env uvars nameOf trProj Delta
      (.const id us info) args recursorPrefix)
    (hlength : args.length = pattern.majorIdx)
    (hcase : NatRecIotaCase pattern major) :
    ∃ (levels : List Lean4Lean.VLevel)
        (captures : (RecursorIotaPattern pattern.recursorName
          pattern.majorIdx pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat)).Path → VExpr),
      Lean4Lean.Pattern.Matches
        (RecursorIotaPattern pattern.recursorName pattern.majorIdx
          pattern.constructorName
          (pattern.constructorParams.toNat +
            pattern.constructorFields.toNat))
        (.app recursorPrefix (VExpr.natLit major)) levels captures :=
  hspine.matches_natRecRulePrefix hpattern.1 hlength hcase

end RawRecursorRulePatternRel

end Ix.Tc
