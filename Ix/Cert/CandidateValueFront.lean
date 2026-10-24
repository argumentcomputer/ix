import Ix.Cert.DefinitionSnapshots
import Ix.Cert.PrefixCore
import IxC.Kernel.Verify.Cached.BridgeC

/-! Unwired whole-candidate value checking. The projected result discards
the temporary pushed FEnv; lookup agreement never equates its physical tail.
This producer checkpoint supplies no Source-origin or value-equality claim. -/
namespace Ix.Cert.CandidateValueFront
open Ix.Kernel Ix.Kernel.Cached Ix.Kernel.Semantics
universe w
variable {md : Mode}

/-- One existing verified whole-body call, returning only its checked body.
The state is threaded within the call; the public boundary below starts fresh. -/
private def bodyC (view : FEnv md) (cv : Ix.Kernel.ConstantVal md) (expected candidate : Ix.Kernel.Expr md)
    (hint : ReducibilityHint) : CheckCM md (Ix.Kernel.Expr md) := do
  let after ← checkDefnValC .verified view { cv with type := expected } expected candidate hint
  match after.env.consts with
  | .defnInfo _ checked _ :: _ => return checked
  | _ => throw (.internal "candidate value checker returned no definition")

def body (view : FEnv md) (cv : Ix.Kernel.ConstantVal md) (expected candidate : Ix.Kernel.Expr md)
    (hint : ReducibilityHint) : Except (CheckError md) (Ix.Kernel.Expr md) :=
  (bodyC view cv expected candidate hint {}).map (·.1)

private theorem choose_bind {α β : Type} (p : Prop) [Decidable p] (x y : CheckCM md α) (f : α → CheckCM md β) :
    ((if p then x else y) >>= f) = (if p then x >>= f else y >>= f) := by split <;> rfl

private theorem fail_bind {α β : Type} (e : CheckError md) (f : α → CheckCM md β) :
    (throw e >>= f : CheckCM md β) = throw e := rfl

/-- Only the body/error (and internal memo result) is transported. The
temporary pushed environments themselves are deliberately not equated. -/
private theorem bodyC_congr {left right : FEnv md} (same : left.find? = right.find?)
    (cv : Ix.Kernel.ConstantVal md) (expected candidate : Ix.Kernel.Expr md) (hint : ReducibilityHint) :
    bodyC left cv expected candidate hint = bodyC right cv expected candidate hint := by
  unfold bodyC checkDefnValC
  simp only [choose_bind, bind_assoc, fail_bind, pure_bind, FEnv.push,
    coreKnotI_congr same, constsResolveFC_congr same]

theorem body_congr {left right : FEnv md} (same : left.find? = right.find?)
    (cv : Ix.Kernel.ConstantVal md) (expected candidate : Ix.Kernel.Expr md) (hint : ReducibilityHint) :
    body left cv expected candidate hint = body right cv expected candidate hint := by
  rw [body, body, bodyC_congr same]

/-- The pure whole-value run supplies every ValueFrontRun conjunct and the
exact checked body. This is not a declaration or native-operation admission. -/
theorem pure_front {env out : Env md} {F : Nat} {cv : Ix.Kernel.ConstantVal md}
    {candidate : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (run : checkDefnVal (fueledOps .verified F) env cv candidate hint = .ok out) :
    ∃ checked, ValueFrontRun .verified F env cv candidate cv.type checked ∧
      out = ⟨.defnInfo cv checked hint :: env.consts⟩ := by
  unfold checkDefnVal at run
  simp only [fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq] at run
  by_cases bounded : candidate.looseBVarsBounded 0 = true
  · simp only [bounded, ↓reduceIte] at run
    cases closed : candidate.hasFvar with
    | true => simp [closed, bind, Except.bind] at run
    | false =>
      simp only [closed, Bool.false_eq_true, ↓reduceIte] at run
      cases annotated : annotateCore .verified env F 0 candidate with
      | error e => simp [annotated, bind, Except.bind] at run
      | ok checked =>
        simp only [annotated, bind, Except.bind] at run
        by_cases levels : checked.allLevelParamsDefined cv.levelParams = true
        · simp only [levels, ↓reduceIte] at run
          by_cases resolved : checked.constsResolve env = true
          · simp only [resolved, ↓reduceIte] at run
            cases inferred : inferTypeCore .verified env F 0 checked with
            | error e => simp [inferred] at run
            | ok type =>
              simp only [inferred] at run
              cases converted : isDefEqCore .verified env F 0 type cv.type with
              | error e => simp [converted] at run
              | ok b =>
                cases b with
                | false => simp [converted] at run
                | true =>
                  simp only [converted, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at run
                  exact ⟨checked, valueFrontRun_of bounded closed annotated levels resolved inferred converted, run.symm⟩
          · simp [resolved] at run
        · simp [levels] at run
  · simp [bounded, bind, Except.bind] at run

private theorem body_front {env : Env md} (wf : EnvWF env)
    {cv : Ix.Kernel.ConstantVal md} {expected candidate checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}
    (headerScoped : Ix.Kernel.Expr.WScoped 0 expected)
    (run : body (mkFEnv env) cv expected candidate hint = .ok checked) :
    ∃ F, ValueFrontRun .verified F env cv candidate expected checked := by
  unfold body at run
  cases cached : bodyC (mkFEnv env) cv expected candidate hint {} with
  | error e => simp [cached, Except.map] at run
  | ok pair =>
    obtain ⟨value, state⟩ := pair
    simp only [cached, Except.map, Except.ok.injEq] at run
    subst value
    unfold bodyC at cached
    obtain ⟨after, mid, actual, projected⟩ := bindC_ok cached
    obtain ⟨_, out, relation, F, pureRun⟩ :=
      (checkDefnValC_sim (mode := .verified) rfl wf headerScoped rfl rfl (CSOK.empty env)) after mid actual
    rw [checkDefnVal_datF] at pureRun
    obtain ⟨value, front, shape⟩ := pure_front pureRun
    have contents := congrArg Env.consts (relation.1.trans shape)
    simp only [contents, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at projected
    obtain ⟨rfl, _⟩ := projected
    exact ⟨F, front⟩

inductive Error where
  | context (message : String)
  | value (error : CheckError .anon)

/-- A generic candidate check, not a Source-form designation. Receipt data
alone is not authentication; the theorem below requires its actual run. -/
def checkAt (r : DefinitionSnapshots.Receipt) (i : Nat) (candidate : Ix.Kernel.Expr .anon) :
    Except Error (Ix.Kernel.Expr .anon) := do
  let s ← (r.snapshot i).mapError .context
  (body s.view s.cv s.expected candidate s.hint).mapError .value

private theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {v : α}
    (h : x.mapError f = .ok v) : x = .ok v := by
  cases x with
  | error e => cases h
  | ok a => cases h; rfl

/-- Real receipt/index/candidate execution produces an independent-fuel
whole value front at the SAME before/cv/expected. All structural and cache
premises are discharged internally; source origin/value equality are absent. -/
theorem checkAt_front (V : Type w) [SetTheory V] {binding limits records blobs hints r}
    (accepted : DefinitionSnapshots.checkReceipt binding limits records blobs hints = .ok r)
    {i : Nat} {cv : Ix.Kernel.ConstantVal .anon} {targetRaw candidate candidateChecked : Ix.Kernel.Expr .anon}
    {hint : ReducibilityHint}
    (atDecl : r.ds.toList[i]? = some (.defnDecl cv targetRaw hint))
    (ran : checkAt r i candidate = .ok candidateChecked) :
    ∃ F before expected targetChecked FB,
      ReferenceFronts.DefinitionFrontAt r.ev r.ds.toList r.env i cv targetRaw hint
        F before expected targetChecked ∧
      ValueFrontRun .verified FB before cv candidate expected candidateChecked := by
  obtain ⟨F, before, expected, targetChecked, front, snapshot, _, _, lookup, _⟩ :=
    DefinitionSnapshots.snapshot_of_check V accepted atDecl
  unfold checkAt at ran
  simp only [snapshot, Except.mapError, bind, Except.bind] at ran
  have checked := mapError_ok ran
  have same : (r.index.restrictTo before.consts.length).find? = (mkFEnv before).find? :=
    funext fun n => (lookup n).trans (mkFEnv_find? before n).symm
  rw [body_congr same] at checked
  have header := front.2.2.2.2.2.1
  obtain ⟨_, _, _, _, bounded, closed, annotated, _, _, _⟩ := header
  have headerScoped := (ConversionValues.annotation_frame annotated closed bounded).1
  obtain ⟨FB, value⟩ := body_front (PrefixCore.prefix_syntax front V).1 headerScoped checked
  exact ⟨F, before, expected, targetChecked, FB, front, value⟩

end Ix.Cert.CandidateValueFront
