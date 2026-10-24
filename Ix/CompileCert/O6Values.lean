import Ix.Cert.CheckedBetaSpine

/-! # Public values for the actual closed O6 recursor branch

The actual pass, generated/recognized image, both raw readings and both
annotations stay linked in the public signature. The baseline's raw guards
and full inference derive the input frame and every checked beta certificate.
The exact annotated-output identity is proved by O6Annotation, not supplied
as a conversion or semantic premise.

Reduction soundness gives the output frame/read/grade and common public
value at each strong model of the SAME prefix environment, with the SAME
level and variable valuation. Neither output nor intermediate-reduct
inference is assumed. This local image-application theorem does not prove
source-recursor/image faithfulness, driver binding, CQ5.4 or CompileCorrect.
-/

namespace Ix.CompileCert.O6Values

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame)
open Ix.Cert.ConversionValues
open O6RecRead

universe w
variable {md : Mode} {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- The actual closed .kRec rewrite preserves the public value of its
checked image application, including Prop and all extra arguments. Frame,
Red and DefEq of the input/step are derived before the model quantifier;
the output frame is supplied by reduction soundness at each such model.

The reader equations/Related witnesses and annotation/inference successes
are explicit boundary obligations. This does not claim the real entrypoint
already supplies them, substitute a post-insertion model, or extend the
result to open occurrences, .recOn or fallback development. -/
theorem o6_rec_values (env : Ix.Kernel.Env md)
    {opt : OptEnv} {o : Occ} {output : Ix.Expr} {r : Ix.Name} {block : OptBlock} {s : RecShape}
    {inp : ViewInput} {all : Array Ix.Name} {view : BlockView} {rv : Ix.RecursorVal}
    {img : Ix.Compile.Image.Image}
    (pass : O6.apply opt o = some output) (kind : classify o.head = some (.kRec, r))
    (blockLookup : opt.blockOf o.head = some block) (shapeLookup : block.shapes.get? r = some s)
    (built : buildView inp all = .ok view) (source : inp.const? r = some (.recInfo rv))
    (generated : view.image inp r = .ok img)
    (recognized : readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors rv.numIndices
      img.value (ImageShape.viewRecInfo view) = some s)
    (universeArity : o.us.size = img.levelParams.size)
    {baseReader outReader : Ix.Kernel.Reader.MemberReader md} {baseWire outWire : Ixon.Expr}
    {baseK outputK baseA outputA baseType : Ix.Kernel.Expr md} {FB FO FI : Nat}
    (baseRead : baseReader.read baseWire = .ok baseK) (outRead : outReader.read outWire = .ok outputK)
    (baseRelated : Rel (keyOf := keyOf) (levelOf := levelOf)
      (Ix.Compile.Canon.mkAppN (Ix.Compile.Canon.substLevels img.levelParams o.us img.value) o.args) baseK)
    (outRelated : Rel (keyOf := keyOf) (levelOf := levelOf) output outputK)
    (noFvars : baseK.hasFvar = false) (bounded : baseK.looseBVarsBounded 0 = true)
    (baseAnn : annotateCore .verified env FB 0 baseK = .ok baseA)
    (outAnn : annotateCore .verified env FO 0 outputK = .ok outputA)
    (baseInfer : inferTypeCore .verified env FI 0 baseA = .ok baseType) :
    Frame 0 baseA ∧ Ix.Kernel.Rules.Red env 0 baseA outputA ∧
      Ix.Kernel.Rules.DefEq env 0 baseA outputA ∧
      ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env)
        (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        Frame 0 outputA ∧ ∃ value,
          Denotes M.model.cval env φ ρ baseA value ∧
          Denotes M.model.cval env φ ρ outputA value := by
  have frame := annotation_frame baseAnn noFvars bounded
  obtain ⟨_, imageA, tail, _, argsA, _, checkedBinders, _, _, _, _, _,
      fit, _, checkedStrip, baseShape, outputShape⟩ :=
    O6Annotation.o6_rec_annotation_layout env pass kind blockLookup shapeLookup
      built source generated recognized universeArity baseRead outRead baseRelated outRelated
      bounded baseAnn outAnn
  have reduction : Ix.Kernel.Rules.Red env 0 baseA outputA := by
    rw [baseShape, outputShape]
    exact Ix.Cert.CheckedBetaSpine.checked_lambda_spine_red checkedStrip fit
      (baseShape ▸ frame) (baseShape ▸ baseInfer)
  refine ⟨frame, reduction, Ix.Kernel.Rules.DefEq.ofRed reduction, ?_⟩
  intro V inst M φ ρ
  obtain ⟨ea, read, grade⟩ := infer_reading M φ frame baseInfer
  obtain ⟨frameOut, _, outTerm, readOut, gradeOut, same⟩ :=
    Model.Rules.red_sound (Model.Rules.RulesInputs.ofSem M.internal φ)
      reduction frame (frame_context M φ frame) read grade
  refine ⟨frameOut, interp V ρ ea, reading_denotes M frame read grade ρ, ?_⟩
  rw [same ρ (Sat_nil V ρ)]
  exact reading_denotes M frameOut readOut gradeOut ρ

end Ix.CompileCert.O6Values
