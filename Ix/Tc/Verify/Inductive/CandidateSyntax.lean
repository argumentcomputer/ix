import Ix.Tc.Verify.Inductive.PositivityTraceAdapter
import Ix.Tc.Verify.Totalization

/-!
# Exact candidate syntax shared by Ix and Lean4Lean

The Theory-level `VExpr` relations used elsewhere in the verification are
semantic: they deliberately forget binder annotations and concrete free-
variable identifiers.  Constructor positivity has one stricter boundary.
Lean4Lean's `isValidIndApp?` inspects the exact kernel `Lean.Expr`, so a
Theory-level definitional-equality result cannot justify that executable
syntax test.

`CandidateSyntaxRel` records the small exact fragment traversed by positivity
after WHNF: variables, sorts, constants, applications, and foralls.  Free
variables and universe levels remain parameterized relations so a concrete
ingress/candidate bridge can choose the two checkers' actual identifiers and
level-parameter representation.  The occurrence theorem below is independent
of those choices and discharges the corresponding field of
`FlatPositivityTraceTransport` without a semantic oracle.
-/

namespace Ix.Tc

/-- Exact correspondence between one Ix positivity expression and one Lean
kernel candidate expression.  This intentionally excludes syntax erased by
the Theory translation (`letE`, literals, projections, and metadata wrappers)
and excludes lambdas, which cannot be a successful mentioned terminal in the
production positivity traversal. -/
inductive CandidateSyntaxRel
    (nameOf : Address → Option Lean.Name)
    (fvarRel : FVarId → Lean.FVarId → Prop)
    (levelRel : KUniv .anon → Lean.Level → Prop) :
    KExpr .anon → Lean.Expr → Prop
  | bvar {index : UInt64} {name : Mode.anon.F Name}
      {info : ExprInfo .anon} :
      CandidateSyntaxRel nameOf fvarRel levelRel
        (.var index name info) (.bvar index.toNat)
  | fvar {ixId : FVarId} {leanId : Lean.FVarId}
      {name : Mode.anon.F Name} {info : ExprInfo .anon} :
      fvarRel ixId leanId →
      CandidateSyntaxRel nameOf fvarRel levelRel
        (.fvar ixId name info) (.fvar leanId)
  | sort {ixLevel : KUniv .anon} {leanLevel : Lean.Level}
      {info : ExprInfo .anon} :
      levelRel ixLevel leanLevel →
      CandidateSyntaxRel nameOf fvarRel levelRel
        (.sort ixLevel info) (.sort leanLevel)
  | const {id : KId .anon} {ixLevels : Array (KUniv .anon)}
      {info : ExprInfo .anon} {leanName : Lean.Name}
      {leanLevels : List Lean.Level} :
      nameOf id.addr = some leanName →
      List.Forall₂ levelRel ixLevels.toList leanLevels →
      CandidateSyntaxRel nameOf fvarRel levelRel
        (.const id ixLevels info) (.const leanName leanLevels)
  | app {ixFn ixArg : KExpr .anon} {leanFn leanArg : Lean.Expr}
      {info : ExprInfo .anon} :
      CandidateSyntaxRel nameOf fvarRel levelRel ixFn leanFn →
      CandidateSyntaxRel nameOf fvarRel levelRel ixArg leanArg →
      CandidateSyntaxRel nameOf fvarRel levelRel
        (.app ixFn ixArg info) (.app leanFn leanArg)
  | forallE {ixName : Mode.anon.F Name}
      {ixBinder : Mode.anon.F Lean.BinderInfo}
      {ixDomain ixBody : KExpr .anon} {info : ExprInfo .anon}
      {leanName : Lean.Name} {leanBinder : Lean.BinderInfo}
      {leanDomain leanBody : Lean.Expr} :
      CandidateSyntaxRel nameOf fvarRel levelRel ixDomain leanDomain →
      CandidateSyntaxRel nameOf fvarRel levelRel ixBody leanBody →
      CandidateSyntaxRel nameOf fvarRel levelRel
        (.all ixName ixBinder ixDomain ixBody info)
        (.forallE leanName leanDomain leanBody leanBinder)

/-- The two physical block representations recognize exactly the same
constant head.  The equality is Boolean because both production occurrence
checks are Boolean and because this avoids importing an injectivity claim for
anonymous addresses or Lean names. -/
def CandidateBlockRel (nameOf : Address → Option Lean.Name)
    (ixAddrs : Array Address) (leanConsts : Array Lean.Expr) : Prop :=
  ∀ {id : KId .anon} {leanName : Lean.Name},
    nameOf id.addr = some leanName →
    ixAddrs.any (fun addr => id.addr == addr) =
      leanConsts.any (fun expression => expression.constName! == leanName)

namespace CandidateSyntax

/-- Reconstruct the named Lean level used by an exact kernel candidate from
Ix's positional anonymous universe representation. -/
def level? (lparams : List Lean.Name) : KUniv .anon → Option Lean.Level
  | .zero _ => some .zero
  | .succ inner _ => return .succ (← level? lparams inner)
  | .max left right _ =>
      return .max (← level? lparams left) (← level? lparams right)
  | .imax left right _ =>
      return .imax (← level? lparams left) (← level? lparams right)
  | .param index _ _ => return .param (← lparams[index.toNat]?)

/-- Exact structural comparison between an anonymous Ix universe and the
named Lean universe used by the candidate checker.  We spell this out instead
of comparing `Lean.Level` values: kernel levels intentionally expose `BEq`
without a global `DecidableEq`/`LawfulBEq` instance. -/
def levelMatches (lparams : List Lean.Name) :
    KUniv .anon → Lean.Level → Bool
  | .zero _, .zero => true
  | .succ ixInner _, .succ leanInner =>
      levelMatches lparams ixInner leanInner
  | .max ixLeft ixRight _, .max leanLeft leanRight =>
      levelMatches lparams ixLeft leanLeft &&
        levelMatches lparams ixRight leanRight
  | .imax ixLeft ixRight _, .imax leanLeft leanRight =>
      levelMatches lparams ixLeft leanLeft &&
        levelMatches lparams ixRight leanRight
  | .param index _ _, .param leanName =>
      match lparams[index.toNat]? with
      | some expected => expected == leanName
      | none => false
  | _, _ => false

/-- Boolean comparison of universe argument lists through `levelMatches`. -/
def levelsMatch (lparams : List Lean.Name) :
    List (KUniv .anon) → List Lean.Level → Bool
  | [], [] => true
  | ixLevel :: ixLevels, leanLevel :: leanLevels =>
      levelMatches lparams ixLevel leanLevel &&
        levelsMatch lparams ixLevels leanLevels
  | _, _ => false

/-- Executable exact-syntax check for the positivity candidate fragment.
Binder names and binder information are intentionally ignored, matching the
metadata-free anonymous ingress representation. -/
def check (nameOf : Address → Option Lean.Name)
    (fvarMatches : FVarId → Lean.FVarId → Bool)
    (lparams : List Lean.Name) :
    KExpr .anon → Lean.Expr → Bool
  | .var index _ _, .bvar leanIndex => decide (index.toNat = leanIndex)
  | .fvar ixId _ _, .fvar leanId => fvarMatches ixId leanId
  | .sort ixLevel _, .sort leanLevel =>
      levelMatches lparams ixLevel leanLevel
  | .const id ixLevels _, .const leanName leanLevels =>
      decide (nameOf id.addr = some leanName) &&
        levelsMatch lparams ixLevels.toList leanLevels
  | .app ixFn ixArg _, .app leanFn leanArg =>
      check nameOf fvarMatches lparams ixFn leanFn &&
        check nameOf fvarMatches lparams ixArg leanArg
  | .all _ _ ixDomain ixBody _,
      .forallE _ leanDomain leanBody _ =>
      check nameOf fvarMatches lparams ixDomain leanDomain &&
        check nameOf fvarMatches lparams ixBody leanBody
  | _, _ => false

private theorem levelsMatch_forall₂
    (lparams : List Lean.Name) :
    ∀ {ixLevels : List (KUniv .anon)} {leanLevels : List Lean.Level},
      levelsMatch lparams ixLevels leanLevels = true →
      List.Forall₂
        (fun ixLevel leanLevel => levelMatches lparams ixLevel leanLevel = true)
        ixLevels leanLevels
  | [], [], _ => .nil
  | ixLevel :: ixLevels, leanLevel :: leanLevels, success => by
      simp only [levelsMatch, Bool.and_eq_true] at success
      exact .cons success.1
        (levelsMatch_forall₂ lparams success.2)

/-- A successful executable syntax comparison yields the proof-relevant
relation consumed by the positivity adapter. -/
theorem rel_of_check
    {nameOf : Address → Option Lean.Name}
    {fvarMatches : FVarId → Lean.FVarId → Bool}
    {lparams : List Lean.Name}
    {ixExpr : KExpr .anon} {leanExpr : Lean.Expr}
    (success : check nameOf fvarMatches lparams ixExpr leanExpr = true) :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => fvarMatches ixId leanId = true)
      (fun ixLevel leanLevel => levelMatches lparams ixLevel leanLevel = true)
      ixExpr leanExpr := by
  induction ixExpr generalizing leanExpr with
  | var index name info =>
      cases leanExpr <;> simp [check] at success
      subst_vars
      exact .bvar
  | fvar ixId name info =>
      cases leanExpr <;> simp [check] at success
      exact .fvar success
  | sort ixLevel info =>
      cases leanExpr <;> simp [check] at success
      exact .sort success
  | const id ixLevels info =>
      cases leanExpr <;> simp [check] at success
      rename_i leanName leanLevels
      exact .const success.1
        (levelsMatch_forall₂ lparams success.2)
  | app ixFn ixArg info ihFn ihArg =>
      cases leanExpr <;> simp [check] at success
      rename_i leanFn leanArg
      exact .app (ihFn success.1) (ihArg success.2)
  | all ixName ixBinder ixDomain ixBody info ihDomain ihBody =>
      cases leanExpr <;> simp [check] at success
      rename_i leanName leanDomain leanBody leanBinder
      exact .forallE (ihDomain success.1) (ihBody success.2)
  | lam | letE | prj | nat | str =>
      cases leanExpr <;> simp [check] at success

end CandidateSyntax

namespace CandidateSyntaxRel

/-- A worklist occurrence scan is the disjunction of scanning its head and
its tail.  This is the reusable induction principle hidden by production's
stack-safe implementation. -/
private theorem mentionsAddrGo_cons (addr : Address) :
    ∀ (expression : KExpr m) (stack : List (KExpr m)),
      exprMentionsAddr.go addr (expression :: stack) =
        (exprMentionsAddr expression addr ||
          exprMentionsAddr.go addr stack)
  | .var .., stack => by
      simp [exprMentionsAddr, exprMentionsAddr.go]
  | .fvar .., stack => by
      simp [exprMentionsAddr, exprMentionsAddr.go]
  | .sort .., stack => by
      simp [exprMentionsAddr, exprMentionsAddr.go]
  | .const id levels info, stack => by
      simp only [exprMentionsAddr_go_const, exprMentionsAddr_equation]
      split <;> simp
  | .app fn argument info, stack => by
      rw [exprMentionsAddr_go_app]
      rw [mentionsAddrGo_cons addr argument (fn :: stack)]
      rw [mentionsAddrGo_cons addr fn stack]
      simp only [exprMentionsAddr_equation, exprMentionsAddr_go_app]
      rw [mentionsAddrGo_cons addr argument [fn]]
      rw [mentionsAddrGo_cons addr fn []]
      simp [Bool.or_assoc, Bool.or_comm]
  | .lam name bi type body info, stack => by
      rw [exprMentionsAddr.go]
      rw [mentionsAddrGo_cons addr body (type :: stack)]
      rw [mentionsAddrGo_cons addr type stack]
      simp only [exprMentionsAddr_equation]
      rw [exprMentionsAddr.go]
      rw [mentionsAddrGo_cons addr body [type]]
      rw [mentionsAddrGo_cons addr type []]
      simp [Bool.or_assoc, Bool.or_comm]
  | .all name bi type body info, stack => by
      rw [exprMentionsAddr.go]
      rw [mentionsAddrGo_cons addr body (type :: stack)]
      rw [mentionsAddrGo_cons addr type stack]
      simp only [exprMentionsAddr_equation]
      rw [exprMentionsAddr.go]
      rw [mentionsAddrGo_cons addr body [type]]
      rw [mentionsAddrGo_cons addr type []]
      simp [Bool.or_assoc, Bool.or_comm]
  | .letE name type value body nonDep info, stack => by
      rw [exprMentionsAddr.go]
      rw [mentionsAddrGo_cons addr body (value :: type :: stack)]
      rw [mentionsAddrGo_cons addr value (type :: stack)]
      rw [mentionsAddrGo_cons addr type stack]
      simp only [exprMentionsAddr_equation]
      rw [exprMentionsAddr.go]
      rw [mentionsAddrGo_cons addr body [value, type]]
      rw [mentionsAddrGo_cons addr value [type]]
      rw [mentionsAddrGo_cons addr type []]
      simp [Bool.or_assoc, Bool.or_comm]
  | .prj id field value info, stack => by
      rw [exprMentionsAddr.go]
      simp only [exprMentionsAddr_equation]
      rw [exprMentionsAddr.go]
      split
      · simp
      · rw [mentionsAddrGo_cons addr value stack]
        rw [mentionsAddrGo_cons addr value []]
        simp
  | .nat .., stack => by
      simp [exprMentionsAddr, exprMentionsAddr.go]
  | .str .., stack => by
      simp [exprMentionsAddr, exprMentionsAddr.go]

private theorem mentionsAddr_app (fn argument : KExpr m)
    (info : ExprInfo m) (addr : Address) :
    exprMentionsAddr (.app fn argument info) addr =
      (exprMentionsAddr fn addr || exprMentionsAddr argument addr) := by
  simp only [exprMentionsAddr_equation, exprMentionsAddr_go_app]
  rw [mentionsAddrGo_cons addr argument [fn]]
  rw [mentionsAddrGo_cons addr fn []]
  simp [Bool.or_comm]

private theorem mentionsAddr_all (name : m.F Name)
    (bi : m.F Lean.BinderInfo) (domain body : KExpr m)
    (info : ExprInfo m) (addr : Address) :
    exprMentionsAddr (.all name bi domain body info) addr =
      (exprMentionsAddr domain addr || exprMentionsAddr body addr) := by
  simp only [exprMentionsAddr_equation]
  rw [exprMentionsAddr.go]
  rw [mentionsAddrGo_cons addr body [domain]]
  rw [mentionsAddrGo_cons addr domain []]
  simp [Bool.or_comm]

private theorem arrayAny_or (values : Array α) (left right : α → Bool) :
    values.any (fun value => left value || right value) =
      (values.any left || values.any right) := by
  rw [← Array.any_toList, ← Array.any_toList, ← Array.any_toList]
  induction values.toList with
  | nil => rfl
  | cons value values ih =>
      simp [ih, Bool.or_assoc, Bool.or_left_comm]

private theorem mentionsAny_app (fn argument : KExpr m)
    (info : ExprInfo m) (addrs : Array Address) :
    exprMentionsAnyAddr (.app fn argument info) addrs =
      (exprMentionsAnyAddr fn addrs || exprMentionsAnyAddr argument addrs) := by
  unfold exprMentionsAnyAddr
  simp only [mentionsAddr_app]
  exact arrayAny_or addrs _ _

private theorem mentionsAny_all (name : m.F Name)
    (bi : m.F Lean.BinderInfo) (domain body : KExpr m)
    (info : ExprInfo m) (addrs : Array Address) :
    exprMentionsAnyAddr (.all name bi domain body info) addrs =
      (exprMentionsAnyAddr domain addrs ||
        exprMentionsAnyAddr body addrs) := by
  unfold exprMentionsAnyAddr
  simp only [mentionsAddr_all]
  exact arrayAny_or addrs _ _

/-- Exact candidate syntax preserves the executable block-occurrence test.
This is intentionally stronger than preservation of Theory semantics:
definitional equality can unfold a constant and therefore does not preserve
the syntactic occurrence decision used by constructor validation. -/
theorem mentionsAnyAddr_eq_hasIndOcc
    {nameOf : Address → Option Lean.Name}
    {fvarRel : FVarId → Lean.FVarId → Prop}
    {levelRel : KUniv .anon → Lean.Level → Prop}
    {ixAddrs : Array Address} {leanConsts : Array Lean.Expr}
    (blocks : CandidateBlockRel nameOf ixAddrs leanConsts)
    (relation : CandidateSyntaxRel nameOf fvarRel levelRel ixExpr leanExpr) :
    exprMentionsAnyAddr ixExpr ixAddrs =
      Lean4Lean.AddInductive.hasIndOcc leanConsts leanExpr := by
  induction relation with
  | bvar => simp [exprMentionsAnyAddr, exprMentionsAddr,
      exprMentionsAddr.go, Lean4Lean.AddInductive.hasIndOcc]
  | fvar => simp [exprMentionsAnyAddr, exprMentionsAddr,
      exprMentionsAddr.go, Lean4Lean.AddInductive.hasIndOcc]
  | sort => simp [exprMentionsAnyAddr, exprMentionsAddr,
      exprMentionsAddr.go, Lean4Lean.AddInductive.hasIndOcc]
  | @const id ixLevels info leanName leanLevels hname levels =>
      simp only [exprMentionsAnyAddr, exprMentionsAddr_equation,
        exprMentionsAddr_go_const, exprMentionsAddr_go_nil,
        Lean4Lean.AddInductive.hasIndOcc]
      have occurrence :
          exprMentionsAddr (.const id ixLevels info) =
            (fun addr => id.addr == addr) := by
        funext addr
        simp [exprMentionsAddr]
      rw [occurrence]
      exact blocks hname
  | app fn arg ihFn ihArg =>
      rw [mentionsAny_app, Lean4Lean.AddInductive.hasIndOcc, ihFn, ihArg]
  | forallE domain body ihDomain ihBody =>
      rw [mentionsAny_all, Lean4Lean.AddInductive.hasIndOcc,
        ihDomain, ihBody]

end CandidateSyntaxRel

end Ix.Tc
