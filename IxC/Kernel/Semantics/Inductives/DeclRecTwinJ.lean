module

public import IxC.Kernel.Semantics.DeclJ
public import IxC.Kernel.Semantics.Inductives.WrapRel
import IxC.Kernel.Verify.Extend.Inversions

@[expose] public section

/-! # Checked constant headers and recursor-twin installation

These judgement records are independent of the native dispatch, so executable twin runs
can enter that dispatch without creating an import cycle.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (CheckMode Env Expr Key Level LevelParam ConstantInfo ConstantVal RecRule
  reservedBasisNames fueledOps)

/-- **`checkConstantVal` over a package**: the front door's guards, the type's
annotation, its scoping, and its typing at a sort; the checked constant carries
the annotated type. -/
def ConstantValCheckJ (J : Judgements md) (env : Env md) (cv cv' : ConstantVal md) : Prop :=
  ∃ type', ConstantValRunJ J env cv type' ∧ cv' = { cv with type := type' }

/-! ## The twin recursor route -/

/-- **One twin recursor rule's stage** over a package: the declared rule's right-hand side is
closed, annotated at the provisioned environment `envSelf`, scoped at the recursor's level
parameters and constants, and free of `let`; the installed rule carries the canonical rule's
constructor, counts, fire mode, parameter blindness, K bit, and the η verdict at the twin's
own name; a plain rule passes `Expr.recRulePlain` at the twin's checked type; a nested rule
matches the twin's major-premise domain; and a single generated right-hand side `rhsG`
(either the canonical rule's own right-hand side, or a closed term typed at `env`) relates
to `rC.rhs` before renaming and to `rW'.rhs` after renaming `f`. -/
def TwinRuleJ (J : Judgements md) (env envSelf : Env md) (f : Key md → Key md)
    (recName : Key md) (lps : List LevelParam) (cvW' : ConstantVal md) (mI rP : Nat)
    (rW rW' rC : RecRule md) : Prop :=
  rW.ctor = rW'.ctor ∧ rW.nfields = rW'.nfields ∧
  rW.rhs.looseBVarsBounded 0 = true ∧ rW.rhs.hasFvar = false ∧
  J.annot envSelf 0 rW.rhs rW'.rhs ∧
  rW'.rhs.allLevelParamsDefined lps = true ∧
  rW'.rhs.constsResolve envSelf = true ∧
  letFree rW'.rhs = true ∧
  rW'.ctor = rC.ctor ∧ rW'.nfields = rC.nfields ∧
  rW'.ctorParams = rC.ctorParams ∧ rW'.fire = rC.fire ∧
  rW'.k = rC.k ∧ rW'.paramsBlind = rC.paramsBlind ∧
  rW'.eta = Ix.Kernel.recRuleEtaOf env.find? recName rC.ctor ∧
  (rW'.fire = .plain → ∀ cvj cnP cnF,
    env.find? rW'.ctor = some (.ctorInfo cvj cnP cnF) →
    Expr.recRulePlain cvW'.type mI rP rW'.ctorParams cvj.levelParams = true) ∧
  (∀ lvls pins, rW'.fire = .nested lvls pins →
    ∃ pre dom body bm D,
      cvW'.type.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i))) ∧
  ∃ rhsG : Expr md,
    WrapRel env.find? rhsG rC.rhs ∧
    WrapRel env.find? (rhsG.renameConsts f) rW'.rhs ∧
    (rhsG = rC.rhs ∨
      (rhsG.hasFvar = false ∧ rhsG.allLevelParamsDefined lps = true ∧
        rhsG.constsResolve env = true ∧ rhsG.looseBVarsBounded 0 = true ∧
        ∃ rty, J.infer env 0 rhsG rty))

/-- **One recursor of a twin recursor block**: the declared constant `cvW`, its checked
annotation `cvW'`, the already-stored canonical recursor `(kC, cvC, mI, rP, rulesC)`, the
declared and checked rule lists `rulesW` and `rulesW'`, and (for a twin of a modeled
recursor) the canonical recursor's stored model companion `model?`. -/
structure TwinRecPart (md : Ix.Kernel.Mode) where
  cvW : ConstantVal md
  cvW' : ConstantVal md
  cvC : ConstantVal md
  kC : Key md
  mI : Nat
  rP : Nat
  rulesW : List (RecRule md)
  rulesW' : List (RecRule md)
  rulesC : List (RecRule md)
  model? : Option (ConstantVal md × Expr md × Ix.Kernel.ReducibilityHint)

/-- The model companion definition copied to a modeled twin's own `.model` key, if any. -/
def TwinRecPart.modelInfo? (w : TwinRecPart md) : Option (ConstantInfo md) :=
  w.model?.map fun (cvm, mval, hint) =>
    .defnInfo ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams, cvm.type⟩ mval hint

/-- Model companion definitions installed before the twin recursors. -/
def twinModels (ws : List (TwinRecPart md)) : List (ConstantInfo md) :=
  ws.filterMap TwinRecPart.modelInfo?

/-- Provisioned rule-less twin recursor entries for annotating mutual twin rules. -/
def twinProv (ws : List (TwinRecPart md)) : List (ConstantInfo md) :=
  ws.map fun w => .recInfo w.cvW' w.mI w.rP []

/-- Installed twin recursor entries carrying their checked rules. -/
def twinRecs (ws : List (TwinRecPart md)) : List (ConstantInfo md) :=
  ws.map fun w => .recInfo w.cvW' w.mI w.rP w.rulesW'

/-- **The twin recursor route over a package**: a non-empty block of recursor records whose
inductive block was already installed earlier in the environment. Each twin `w` checks its
declared constant `w.cvW` to `w.cvW'`, names a stored canonical recursor `w.kC` with the same
level parameters and counts `(w.mI, w.rP)`, shares a common generated type `tyG` under
`WrapRel`, and checks its rules against `w.rulesC` up to `WrapRel` and the canonical-to-twin
peer renaming `f`. If `w.kC` is a modeled recursor (`w.model? = some …`), its stored model
companion is copied to `auxKey w.cvW.name .model` so `HasModel` holds on the twin; if `w.kC`
is native or basis (`w.model? = none`), `w.kC` has no model companion and the twin's major
premise domain has the canonical head and arguments. -/
def DeclRecTwinRunJ (J : Judgements md) (env : Env md) (block : List (ConstantInfo md))
    (env₂ : Env md) : Prop :=
  ∃ (ws : List (TwinRecPart md)) (f : Key md → Key md),
    ws ≠ [] ∧
    block = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) ∧
    let envM : Env md := ⟨twinModels ws ++ env.consts⟩
    let envSelf : Env md := ⟨twinProv ws ++ envM.consts⟩
    env₂ = ⟨twinRecs ws ++ envM.consts⟩ ∧
    ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup ∧
    (∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none) ∧
    (∀ k, f k = k ∨ ∃ w' ∈ ws, k = w'.kC ∧ f k = w'.cvW.name) ∧
    ∀ w ∈ ws,
      ConstantValCheckJ J env w.cvW w.cvW' ∧
      letFree w.cvW'.type = true ∧
      env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) ∧
      w.cvW.levelParams = w.cvC.levelParams ∧
      (match w.model? with
        | some (cvm, mval, hint) =>
          env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint)
        | none =>
          (∀ cvm mval hint,
            env.find? (Ix.Kernel.auxKey w.kC .model) ≠ some (.defnInfo cvm mval hint)) ∧
          (∀ bsW domW bodyW bmW,
            w.cvW'.type.stripPis w.mI = some (bsW, .forallE domW bodyW bmW) →
            ∃ bsC domC bodyC bmC,
              w.cvC.type.stripPis w.mI = some (bsC, .forallE domC bodyC bmC) ∧
              domW.getAppFn = domC.getAppFn ∧
              domW.getAppArgs = domC.getAppArgs)) ∧
      (∃ tyG : Expr md,
        WrapRel env.find? tyG w.cvC.type ∧
        WrapRel env.find? tyG w.cvW'.type ∧
        (tyG = w.cvC.type ∨
          (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
            tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
            ∃ sty, J.infer env 0 tyG sty))) ∧
      w.rulesW.length = w.rulesW'.length ∧
      Forall₂ (fun (p : RecRule md × RecRule md) rC =>
        TwinRuleJ J env envSelf f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC)
        (w.rulesW.zip w.rulesW') w.rulesC

theorem ConstantValCheckJ.fresh {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : env.find? cv.name = none := by
  obtain ⟨_, hrun, -⟩ := h
  exact Option.isNone_iff_eq_none.mp hrun.1

theorem ConstantValCheckJ.shape {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : cv.name.isProjFnShape = false := by
  obtain ⟨_, hrun, -⟩ := h
  exact hrun.2.2.1

theorem ConstantValCheckJ.name_eq {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') : cv'.name = cv.name := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

theorem ConstantValCheckJ.levelParams_eq {J : Judgements md} {env : Env md}
    {cv cv' : ConstantVal md} (h : ConstantValCheckJ J env cv cv') :
    cv'.levelParams = cv.levelParams := by
  obtain ⟨_, -, rfl⟩ := h
  rfl

/-- **A constant check's facts** (`checkConstantVal_inv` over a package), in the
kernel inversion's order. -/
theorem ConstantValCheckJ.inv {J : Judgements md} {env : Env md} {cv cv' : ConstantVal md}
    (h : ConstantValCheckJ J env cv cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    LevelParam.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      J.annot env 0 cv.type type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      J.infer env 0 type stype ∧
      J.sort env 0 stype u ∧
      cv' = { cv with type := type } := by
  obtain ⟨type, ⟨hf, hres, hpsh, hnd, hlbt, hitf, hann, htp, htr, stype, u, hst, hsort⟩, rfl⟩ := h
  exact ⟨Option.isNone_iff_eq_none.mp hf, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann,
    htp, htr, hst, hsort, rfl⟩


theorem constantValCheckJ_of_run {μ : CheckMode} {F : Nat} {env : Env md} {cv cv' : ConstantVal md}
    (h : Ix.Kernel.checkConstantVal (fueledOps μ F) env cv = .ok cv') :
    ConstantValCheckJ (runJ μ F) env cv cv' := by
  obtain ⟨hfind, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := Ix.Kernel.checkConstantVal_inv h
  exact ⟨type, ⟨Option.isNone_iff_eq_none.mpr hfind, hres, hpsh, hnd, hlbt, hitf,
    hann, htp, htr, ⟨stype, u, hst, hsort⟩⟩, rfl⟩

end Ix.Kernel.Semantics
