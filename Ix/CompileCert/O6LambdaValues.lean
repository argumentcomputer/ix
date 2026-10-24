import Ix.CompileCert.O6Opened
import Ix.Cert.LambdaMarkers

/-! # Whole-lambda values for the actual O6 rewrite

The header and BOTH real value fronts provide additional checker evidence
beyond the opened-body theorem. They compare types against one expected
type in the same prefix env, not the values against each other. Within
each supplied StrongModel, marker agreement closes the derived body DefEq
through the actual common opener. No model existence or inhabited binder
context is assumed; other contexts and pass families remain separate.
-/

namespace Ix.CompileCert.O6LambdaValues

open Ix.Kernel Ix.Kernel.Semantics
open Ix.Cert.ConversionValues
open O6RecRead

universe w
variable {md : Mode} {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- The actual O6 step under one common lambda context preserves its whole
public value. The two real value fronts and minimal header front must be
supplied by SourceFormInfers/target admission in this exact prefix env.
Their production discharge is not asserted here or replaced by a semantic
premise. Whole DefEq and values stay INSIDE each supplied model's scope. -/
theorem o6_rec_under_lam_values (env : Ix.Kernel.Env md)
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
    {baseK outputK : Ix.Kernel.Expr md}
    (baseRead : baseReader.read baseWire = .ok baseK) (outRead : outReader.read outWire = .ok outputK)
    (baseRelated : Rel (keyOf := keyOf) (levelOf := levelOf)
      (Ix.Compile.Canon.mkAppN (Ix.Compile.Canon.substLevels img.levelParams o.us img.value) o.args) baseK)
    (outRelated : Rel (keyOf := keyOf) (levelOf := levelOf) output outputK)
    {cv : Ix.Kernel.ConstantVal md}
    {expected headerSortType rawDom wholeBaseA wholeOutA : Ix.Kernel.Expr md}
    {rawMeta : BinderMeta} {FA FT FB FO : Nat}
    (headerClosed : cv.type.hasFvar = false)
    (headerBounded : cv.type.looseBVarsBounded 0 = true)
    (headerAnn : annotateCore .verified env FA 0 cv.type = .ok expected)
    (headerInfer : inferTypeCore .verified env FT 0 expected = .ok headerSortType)
    (baseFront : ValueFrontRun .verified FB env cv
      (.lam rawDom baseK rawMeta) expected wholeBaseA)
    (outFront : ValueFrontRun .verified FO env cv
      (.lam rawDom outputK rawMeta) expected wholeOutA) :
    ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env),
      Ix.Kernel.Rules.DefEq env 0 wholeBaseA wholeOutA ∧
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        ∃ value, Denotes M.model.cval env φ ρ wholeBaseA value ∧
          Denotes M.model.cval env φ ρ wholeOutA value := by
  obtain ⟨_, baseInfer, _⟩ := baseFront.2.2.2.2.2
  obtain ⟨domA, leftOpen, rightOpen, _, pwL, pwR, _, _, _, _, _, _, _, _,
      _, rightAnn, _, _, baseShape, outShape, domainFrame, _, leftReopen, _, _, bodyEq⟩ :=
    O6Opened.o6_rec_under_lam_opened_red env pass kind blockLookup shapeLookup
      built source generated recognized universeArity baseRead outRead baseRelated outRelated
      baseFront.2.1 baseFront.1 baseFront.2.2.1 outFront.2.2.1 baseInfer
  have outNo := outFront.2.1
  have outBound := outFront.1
  simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at outNo
  simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at outBound
  have rightReopen := O6Opened.annotation_reopen outNo.2 outBound.2 domainFrame rightAnn
  intro V inst M
  have markers : pwL = pwR := Ix.Cert.LambdaMarkers.lambda_markers_eq_of_fronts M
    headerClosed headerBounded headerAnn headerInfer (baseShape ▸ baseFront) (outShape ▸ outFront)
  have conversion : Ix.Kernel.Rules.DefEq env 0 wholeBaseA wholeOutA := by
    rw [baseShape, outShape]
    refine .lam .refl ?_ markers rfl
    simpa only [leftReopen, rightReopen] using bodyEq
  exact ⟨conversion, fun φ ρ => valueFront_defeq_values M baseFront outFront conversion φ ρ⟩

end Ix.CompileCert.O6LambdaValues
