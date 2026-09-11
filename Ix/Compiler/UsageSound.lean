import Ix.Compiler.Ixon.UsageCheck
import Ix.Compiler.EraseValidator

/-!
# Usage-checker non-interference at the erasure boundary

This module connects three independently executable facts:

1. `UsageCheck.check` computes zero use for every binder the eraser drops;
2. `PErase` certifies the exact executable erasure and deliberately leaves
   dropped runtime environment slots unconstrained;
3. two successful source runs related to the same erased run therefore have
   one common observable target value.

The result is intentionally an erasure observation, not raw source-value
equality.  Raw equality is false for closures: changing an unused captured
slot changes the closure's stored environment even though no erased program
can observe it.  Sharing one `IxIR0.Value` witness is the appropriate
semantic quotient and composes directly with the existing simulation.

Both source runs are assumed successful.  Ixon is weak CBV and still
evaluates ghost arguments; termination/error irrelevance needs the future
typed totality bridge, while the forward-simulation theorem only needs the
successful-run direction proved here.
-/

namespace Ix.Compiler.UsageSound

open Ix.Compiler.Ixon (Expr Owned Uses)
open Ix.Compiler.Sim

namespace UC

open Ix.Compiler.Ixon.UsageCheck

/-- The checker and eraser use extensionally identical sort-telescope tests.
Keeping this theorem explicit prevents their separately layered executable
definitions from drifting. -/
theorem erasureSortLike_eq_sortLike (sharing : Array Expr) (fuel : Nat)
    (expression : Expr) :
    erasureSortLike sharing fuel expression =
      Erase.sortLike sharing fuel expression := by
  induction fuel generalizing expression with
  | zero => rfl
  | succ fuel ih =>
    cases expression <;>
      simp only [erasureSortLike, Erase.sortLike]
    case all uses owned domain codomain => exact ih codomain
    case share index =>
      cases sharing[index.toNat]? with
      | none => rfl
      | some target => exact ih target

/-- Consequently the checker's executable drop classification is exactly the
eraser's, including fuel behavior through sharing indirections. -/
theorem erasureDropsBinder_eq_dropBinder (sharing : Array Expr) (fuel : Nat)
    (uses : Uses) (domain : Expr) :
    erasureDropsBinder sharing fuel uses domain =
      Erase.dropBinder sharing fuel uses domain := by
  simp only [erasureDropsBinder, Erase.dropBinder,
    erasureSortLike_eq_sortLike]

/-- Logical view of the checker's "head binder computed zero" fact.  The
existential usage vector is retained inside the proposition so later typed
extensions can attach their runtime-occurrence relation to the same witness. -/
inductive ComputedErasedHead (ctx : CheckCtx) (fuel : Nat)
    (world : Owned) (worlds : List Owned) (body : Expr) : Prop where
  | mk {bodyUses : UseVec} {bodyOwned : Owned} {entry : VarUse}
      {rest : UseVec} :
      check ctx fuel false (world :: worlds) body =
        .ok (bodyUses, bodyOwned) →
      bodyUses = entry :: rest →
      entry.uses = .erased →
      ComputedErasedHead ctx fuel world worlds body

/-- Successful checking of a lambda classified as dropped constructs the
proof-relevant computed-zero witness for its body. -/
theorem ComputedErasedHead.of_checkedLambda {ctx : CheckCtx} {fuel : Nat}
    {worlds : List Owned} {uses : Uses} {domain body : Expr}
    {outerUses : UseVec} {owned : Owned}
    (hdrop : erasureDropsBinder ctx.sharing fuel uses domain = true)
    (hcheck : check ctx (fuel + 1) false worlds (.lam uses domain body) =
      .ok (outerUses, owned)) :
    ComputedErasedHead ctx fuel (worldOf uses) worlds body := by
  obtain ⟨bodyUses, bodyOwned, entry, rest, hbody, hhead, herased⟩ :=
    check_lam_dropped_entry_erased hdrop hcheck
  have hshape : bodyUses = entry :: rest := headEntry_ok_iff.mp hhead
  exact .mk hbody hshape herased

end UC

/-- Two source values are indistinguishable after erasure when both relate to
the same target value.  This intentionally identifies sort/pi/neutral values
with `◻` and closures whose only differences live in dropped captures. -/
def ErasureObsEq (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (left right : Ixon.Eval.Value) : Prop :=
  ∃ target, ValRel ectx ictx left target ∧ ValRel ectx ictx right target

theorem ErasureObsEq.symm {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {left right : Ixon.Eval.Value}
    (h : ErasureObsEq ectx ictx left right) :
    ErasureObsEq ectx ictx right left := by
  obtain ⟨target, hleft, hright⟩ := h
  exact ⟨target, hright, hleft⟩

/-- Semantic non-interference for a checker-computed erased head slot.

`leftEnv` and `rightEnv` may contain arbitrary, unrelated source values in
every `false` mask position.  Both environments relate to one target
environment, and the exact body erasure is certified.  If both source runs
succeed, their results share one erased observation. -/
theorem computedErased_eval_noninterference
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {F : Ixon.Eval.Frame} {sc : Option (Ixon.Address × Nat)}
    {mask : List Bool} {leftEnv rightEnv : List Ixon.Eval.Value}
    {targetEnv : List IxIR0.Value} {body : Expr} {targetBody : IxIR0.Expr}
    {leftFuel rightFuel : Nat} {leftValue rightValue : Ixon.Eval.Value}
    {checkCtx : Ixon.UsageCheck.CheckCtx} {checkFuel : Nat}
    {world : Owned} {worlds : List Owned}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (_computed : UC.ComputedErasedHead checkCtx checkFuel world worlds body)
    (herased : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr
      (false :: mask) body targetBody)
    (hleftEnv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr
      (false :: mask) leftEnv targetEnv)
    (hrightEnv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr
      (false :: mask) rightEnv targetEnv)
    (hleft : Ixon.Eval.eval ectx leftFuel F leftEnv body = .ok leftValue)
    (hright : Ixon.Eval.eval ectx rightFuel F rightEnv body =
      .ok rightValue) :
    ErasureObsEq ectx ictx leftValue rightValue := by
  obtain ⟨leftTargetFuel, leftTarget, hleftTarget, hleftRel⟩ :=
    erasure_sim hstrict horacles hleft herased hleftEnv
  obtain ⟨rightTargetFuel, rightTarget, hrightTarget, hrightRel⟩ :=
    erasure_sim hstrict horacles hright herased hrightEnv
  let joinedFuel := Nat.max leftTargetFuel rightTargetFuel
  have hleftJoined :
      IxIR0.eval ictx joinedFuel targetEnv targetBody = .ok leftTarget :=
    IxIR0.eval_mono (Nat.le_max_left _ _) hleftTarget
  have hrightJoined :
      IxIR0.eval ictx joinedFuel targetEnv targetBody = .ok rightTarget :=
    IxIR0.eval_mono (Nat.le_max_right _ _) hrightTarget
  have htarget : leftTarget = rightTarget := by
    exact Except.ok.inj (hleftJoined.symm.trans hrightJoined)
  subst rightTarget
  exact ⟨leftTarget, hleftRel, hrightRel⟩

/-! ## Contentful dropped-variable witness

`wrapper` binds a sort-like `many` parameter and passes the bound variable to
the sort-like parameter of `consumer`.  UsageCheck computes that occurrence
as zero, erasure emits `◻`, and the proof-producing validator certifies the
exact output.  Source environments containing the distinct runtime literals
`7̂` and `8̂` both produce the contentful `9̂` result and share the same
erased observation.
-/

namespace DroppedVariableFixture

private theorem exceptOkBind {error value result : Type}
    (input : value) (next : value → Except error result) :
    (Except.ok input >>= next) = next input := rfl

private theorem exceptOkDiscard {error value : Type} (input : value) :
    discard (Except.ok input : Except error value) =
      Except.ok PUnit.unit := rfl

private def addrOf (byte : UInt8) : Ixon.Address :=
  Ixon.Address.replicate byte

private def consumerAddress : Ixon.Address := addrOf 0xE0
private def wrapperAddress : Ixon.Address := addrOf 0xE1
private def resultBlob : Ixon.Address := addrOf 0xE2
private def argumentBlob : Ixon.Address := addrOf 0xE3

private def consumer : Ixon.Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .unique (.sort 0) (.sort 0)
        value := .lam .many (.sort 0) (.nat 0) }
    sharing := #[], refs := #[resultBlob], univs := #[.zero] }

private def wrapperBody : Expr :=
  .app (.ref 0 #[]) (.var 0)

private def wrapper : Ixon.Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .unique (.sort 0) (.sort 0)
        value := .lam .many (.sort 0) wrapperBody }
    sharing := #[], refs := #[consumerAddress], univs := #[.zero] }

private def constants : List (Ixon.Address × Ixon.Constant) :=
  [(consumerAddress, consumer), (wrapperAddress, wrapper)]

private def resolve : Ixon.Address → Option Ixon.Constant := fun address =>
  (constants.find? fun entry => entry.1 == address).map (·.2)

private def ectx : Ixon.Eval.EvalCtx :=
  { resolve
    blobs := fun address =>
      if address = resultBlob then some (.natB 9)
      else if address = argumentBlob then some (.natB 7)
      else none }

private def consumerTarget : IxIR0.Expr :=
  .lam .many (.lit (.nat 9))

private def wrapperTargetBody : IxIR0.Expr :=
  .app (.ref consumerAddress) .erased

private def target : List (Ixon.Address × IxIR0.Decl) :=
  [ (consumerAddress, .defn .unique consumerTarget)
  , (wrapperAddress, .defn .unique (.lam .many wrapperTargetBody)) ]

private def ictx : IxIR0.Ctx :=
  { env := IxIR0.Env.ofList target }

private theorem oracleRel : OracleRel ectx ictx :=
  OracleRel.of_externFree (by
    intro address
    rfl)

private def consumerCheckCtx : Ixon.UsageCheck.CheckCtx :=
  { resolve, refs := consumer.refs }

private def wrapperCheckCtx : Ixon.UsageCheck.CheckCtx :=
  { resolve, refs := wrapper.refs }

#guard (match Ixon.UsageCheck.checkConstant resolve consumer 100 with
  | .ok () => true
  | .error _ => false)

#guard (match Ixon.UsageCheck.checkConstant resolve wrapper 100 with
  | .ok () => true
  | .error _ => false)

#guard (match Erase.eraseProgram (EraseValidator.eraseCtxOf ectx)
    constants 100 with
  | .ok declarations => declarations == target
  | .error _ => false)

#guard (match EraseValidator.certifyProgram ectx constants
    [consumerAddress, wrapperAddress] 100 100 with
  | .ok certificate => certificate.target == target &&
      certificate.coverage.length == 2
  | .error _ => false)

private theorem consumerCovered : Covered ectx ictx consumerAddress := by
  apply EraseValidator.covered_of_validate (db := []) (fuel := 100)
  decide

private def consumerCoverage : EraseValidator.CoverageDB ectx ictx :=
  [{ address := consumerAddress, covered := consumerCovered }]

private theorem wrapperCovered : Covered ectx ictx wrapperAddress := by
  apply EraseValidator.covered_of_validate
    (db := consumerCoverage) (fuel := 100)
  decide

private def coverage : EraseValidator.CoverageDB ectx ictx :=
  [ { address := wrapperAddress, covered := wrapperCovered }
  , { address := consumerAddress, covered := consumerCovered } ]

private def cover : EraseValidator.CoverOracle ectx ictx :=
  coverage.oracle

private def wrapperFrame : Ixon.Eval.Frame :=
  Ixon.Eval.Frame.ofConst wrapper

private theorem resolveConsumer :
    resolve consumerAddress = some consumer := by
  simp [resolve, constants]

private def wrapperDemand : Ixon.UsageCheck.Demand :=
  { uses := .many, owned := .unique, dropped := true }

private theorem wrapperExpandHead :
    Ixon.UsageCheck.expandShareE wrapperCheckCtx 98 (.ref 0 #[]) =
      .ok (.ref 0 #[]) := by
  rfl

private theorem wrapperHeadTelescope :
    Ixon.UsageCheck.telescopeOfHead wrapperCheckCtx 98 (.ref 0 #[]) =
      .ok [wrapperDemand] := by
  simp [Ixon.UsageCheck.telescopeOfHead, wrapperCheckCtx, wrapper,
    resolveConsumer, Ixon.UsageCheck.constTypeSharing, consumer,
    Ixon.UsageCheck.telescopeOf, wrapperDemand,
    Ixon.UsageCheck.erasureDropsBinder,
    Ixon.UsageCheck.erasureSortLike]

private theorem wrapperBaseCheck :
    Ixon.UsageCheck.check wrapperCheckCtx 98 false [.shared]
      (.ref 0 #[]) = .ok ([{}], .shared) := by
  rw [Ixon.UsageCheck.check.eq_def]
  simp [wrapperCheckCtx, wrapper, Ixon.UsageCheck.UseVec.zeros]

private theorem wrapperGhostArgumentCheck :
    Ixon.UsageCheck.check wrapperCheckCtx 97 true [.shared]
      (.var 0) = .ok ([{}], .shared) := by
  rw [Ixon.UsageCheck.check.eq_def]
  rfl

private theorem wrapperArgumentsCheck :
    Ixon.UsageCheck.checkArgs wrapperCheckCtx 98 false [.shared]
      [wrapperDemand] 0 [.var 0] [{}] = .ok [{}] := by
  rw [Ixon.UsageCheck.checkArgs.eq_def]
  dsimp only [wrapperDemand]
  rw [wrapperGhostArgumentCheck]
  change Ixon.UsageCheck.checkArgs wrapperCheckCtx 97 false [.shared]
    [wrapperDemand] 1 [] [{}] = .ok [{}]
  rw [Ixon.UsageCheck.checkArgs.eq_def]

private theorem wrapperBodyCheck :
    Ixon.UsageCheck.check wrapperCheckCtx 99 false [.shared]
      wrapperBody = .ok ([{}], .unique) := by
  dsimp only [wrapperBody]
  rw [Ixon.UsageCheck.check.eq_def]
  dsimp only [Expr.collectApp]
  rw [wrapperExpandHead]
  simp only [exceptOkBind]
  rw [wrapperHeadTelescope]
  simp only [exceptOkBind]
  rw [wrapperBaseCheck]
  simp only [exceptOkBind]
  simp only [List.nil_append]
  rw [wrapperArgumentsCheck]
  simp only [exceptOkBind]
  rfl

private theorem wrapperLambdaCheck :
    Ixon.UsageCheck.check wrapperCheckCtx 100 false []
      (.lam .many (.sort 0) wrapperBody) = .ok ([], .unique) := by
  rw [Ixon.UsageCheck.check.eq_def]
  dsimp only
  have domainCheck :
      Ixon.UsageCheck.check wrapperCheckCtx 99 true [] (.sort 0) =
        .ok ([], .shared) := by
    rw [Ixon.UsageCheck.check.eq_def]
    rfl
  rw [domainCheck]
  simp only [exceptOkDiscard, exceptOkBind,
    Ixon.UsageCheck.worldOf]
  rw [wrapperBodyCheck]
  rfl

private def consumerClosure : Ixon.Eval.Value :=
  .closV .many (Ixon.Eval.Frame.ofConst consumer) [] (.sort 0) (.nat 0)

private theorem resultBlobResolved :
    ectx.blobs resultBlob = some (.natB 9) := by
  simp [ectx]

private theorem consumerReferenceEval :
    Ixon.Eval.evalRef ectx 98 consumerAddress [] =
      .ok consumerClosure := by
  rw [Ixon.Eval.evalRef.eq_def]
  simp only [ectx, resolveConsumer, consumer,
    Ixon.Eval.guardLvls, Ixon.Eval.unfoldable]
  rw [Ixon.Eval.eval.eq_def]
  rfl

private theorem wrapperFunctionEval (env : List Ixon.Eval.Value) :
    Ixon.Eval.eval ectx 99 wrapperFrame env (.ref 0 #[]) =
      .ok consumerClosure := by
  rw [Ixon.Eval.eval.eq_def]
  simp only [wrapperFrame, wrapper, Ixon.Eval.evalUnivArgs]
  exact consumerReferenceEval

private theorem wrapperArgumentEval (argument : Ixon.Eval.Value) :
    Ixon.Eval.eval ectx 99 wrapperFrame [argument] (.var 0) =
      .ok argument := by
  rw [Ixon.Eval.eval.eq_def]
  rfl

private theorem consumerApply (argument : Ixon.Eval.Value) :
    Ixon.Eval.apply ectx 99 consumerClosure argument =
      .ok (.litV (.natL 9)) := by
  rw [Ixon.Eval.apply.eq_def]
  dsimp only [consumerClosure]
  rw [Ixon.Eval.eval.eq_def]
  change (match ectx.blobs resultBlob with
    | some (.natB n) =>
        Except.ok (Ixon.Eval.Value.litV (Ixon.Eval.Lit.natL n))
    | some (.strB _) => Except.error
        (Ixon.Eval.Err.stuck "nat literal address holds a string blob")
    | none => Except.error (Ixon.Eval.Err.unknownBlob resultBlob)) =
      Except.ok (Ixon.Eval.Value.litV (Ixon.Eval.Lit.natL 9))
  rw [resultBlobResolved]

private theorem wrapperBodyEval (argument : Ixon.Eval.Value) :
    Ixon.Eval.eval ectx 100 wrapperFrame [argument] wrapperBody =
      .ok (.litV (.natL 9)) := by
  dsimp only [wrapperBody]
  rw [Ixon.Eval.eval.eq_def]
  dsimp only
  rw [wrapperFunctionEval]
  rw [wrapperArgumentEval]
  exact consumerApply argument

private theorem wrapperBodyPErase :
    PErase ectx ictx none wrapperFrame.refs wrapperFrame.selfMuts
      wrapperFrame.selfAddr [false]
      wrapperBody wrapperTargetBody := by
  apply EraseValidator.related_of_validateExpr
    (cover := cover) (fuel := 100)
  decide

private theorem wrapperComputed :
    UC.ComputedErasedHead wrapperCheckCtx 99 .shared [] wrapperBody := by
  apply UC.ComputedErasedHead.of_checkedLambda
    (uses := .many) (domain := .sort 0)
    (outerUses := []) (owned := .unique)
  · rfl
  · exact wrapperLambdaCheck

private theorem leftEnv :
    EnvRel ectx ictx none wrapperFrame.refs wrapperFrame.selfMuts
      wrapperFrame.selfAddr [false]
      [.litV (.natL 7)] [.erased] :=
  .drop .nil

private theorem rightEnv :
    EnvRel ectx ictx none wrapperFrame.refs wrapperFrame.selfMuts
      wrapperFrame.selfAddr [false]
      [.litV (.natL 8)] [.erased] :=
  .drop .nil

/-- Non-degenerate non-interference instance: the dropped slot changes from
`7̂` to `8̂`, while both checked source executions share target result `9̂`. -/
theorem droppedVariableOccurrenceNoninterference :
    ErasureObsEq ectx ictx (.litV (.natL 9)) (.litV (.natL 9)) := by
  apply computedErased_eval_noninterference
    (F := wrapperFrame) (mask := [])
    (leftEnv := [.litV (.natL 7)])
    (rightEnv := [.litV (.natL 8)]) (targetEnv := [.erased])
    ⟨rfl, rfl⟩ oracleRel wrapperComputed wrapperBodyPErase leftEnv rightEnv
    (leftFuel := 100) (rightFuel := 100)
  · exact wrapperBodyEval _
  · exact wrapperBodyEval _

private def entryFrame : Ixon.Eval.Frame :=
  { refs := #[wrapperAddress, argumentBlob] }

private def sourceEntry : Expr :=
  .app (.ref 0 #[]) (.nat 1)

private def targetEntry : IxIR0.Expr :=
  .app (.ref wrapperAddress) .erased

private def entryTables : Erase.ETables :=
  { refs := entryFrame.refs }

private theorem entryPErase :
    PErase ectx ictx none entryFrame.refs #[] none [] sourceEntry
      targetEntry := by
  apply EraseValidator.related_of_validateExpr
    (cover := cover) (fuel := 100)
  decide

/-- Whole-expression forward simulation for the same checked, certified
dropped-variable occurrence. -/
theorem droppedVariableOccurrenceSim {fuel : Nat} {value : Ixon.Eval.Value}
    (hsource : Ixon.Eval.eval ectx fuel entryFrame [] sourceEntry =
      .ok value) :
    ∃ targetFuel targetValue,
      IxIR0.eval ictx targetFuel [] targetEntry = .ok targetValue ∧
      ValRel ectx ictx value targetValue :=
  erasure_sim_closed ⟨rfl, rfl⟩ oracleRel hsource entryPErase

#guard (match Ixon.Eval.eval ectx 100 entryFrame [] sourceEntry with
  | .ok (.litV (.natL 9)) => true
  | _ => false)

#guard (match IxIR0.eval ictx 100 [] targetEntry with
  | .ok (.lit (.nat 9)) => true
  | _ => false)

end DroppedVariableFixture

end Ix.Compiler.UsageSound
