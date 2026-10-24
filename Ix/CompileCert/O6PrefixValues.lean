import Ix.Cert.RuleInputValues
import Ix.Cert.PrefixNatOps
import Ix.CompileCert.O6TelescopeValues

/-! # Indexed O6 values at the supplied final interpretation

The actual target index supplies its prefix, header and output front.
One full baseline front uses that SAME prefix/header. The proved rule
inputs close the existing telescope conversion under each supplied final
model, and both checked subjects denote its exact constant value in envA.
Actual source/translation/image provenance remains a producer obligation.
-/

namespace Ix.CompileCert.O6PrefixValues

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert Ix.Cert.ConversionValues Ix.Cert.ReferenceFronts
open O6RecRead O6Annotation O6Telescope

universe w
variable {md : Mode} {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- The arbitrary shared telescope's checked baseline and actual stored
output both denote the supplied FINAL model's exact constant value. All
header/output facts come from the actual target front; the only additional
checking input is the real whole baseline front in that same prefix.
No prefix StrongModel, semantic equality or new checker flow is assumed. -/
theorem o6_rec_under_telescope_final_values
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
    {ev : Evidences md} {ds : List (Declaration md)} {envA before : Ix.Kernel.Env md}
    {i F FB : Nat} {cv : Ix.Kernel.ConstantVal md} {hint : ReducibilityHint}
    {bs : List (Ix.Kernel.Expr md × BinderMeta)} {expected wholeBaseA wholeOutA : Ix.Kernel.Expr md}
    (target : DefinitionFrontAt ev ds envA i cv (wrapLams bs outputK) hint F before expected wholeOutA)
    (baseline : ValueFrontRun .verified FB before cv (wrapLams bs baseK) expected wholeBaseA) :
    ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA),
      Ix.Kernel.Rules.DefEq before 0 wholeBaseA wholeOutA ∧
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        Denotes M.model.cval envA φ ρ wholeBaseA (M.model.cval cv.name φ) ∧
        Denotes M.model.cval envA φ ρ wholeOutA (M.model.cval cv.name φ) := by
  have targetRun := target
  obtain ⟨_, _, _, _, _, header, outputFront, _⟩ := targetRun
  obtain ⟨_, _, _, _, headerBounded, headerClosed, headerAnn, _, _,
      headerType, _, headerInfer, _⟩ := header
  obtain ⟨_, baseInfer, _⟩ := baseline.2.2.2.2.2
  obtain ⟨_, outInfer, _⟩ := outputFront.2.2.2.2.2
  obtain ⟨As, _, _, _, _, _, _, trace, _, _, _, leafL, leafR, _, _, _, _, leafEq, _⟩ :=
    O6TelescopeOpened.o6_rec_under_telescope_opened_red.{w} before pass kind blockLookup shapeLookup
      built source generated recognized universeArity baseRead outRead baseRelated outRelated
      baseline.2.1 baseline.1 baseline.2.2.1 outputFront.2.2.1 baseInfer
  have len := DomainTrace.length trace
  have empty (e : Ix.Kernel.Expr md) : e.instantiateList (openers 0 []) = e := by
    simp only [openers, List.zipIdx_nil, List.map_nil, List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil]
  intro V _ M
  obtain ⟨core, acvalEq, publicEq, _, inputs, targetPackage⟩ := target.final_prefix_rules_inputs V M
  have markers := RuleInputValues.markers_of_fronts core inputs
    headerClosed headerBounded headerAnn headerInfer baseline outputFront
  have conversion : Ix.Kernel.Rules.DefEq before 0 wholeBaseA wholeOutA :=
    O6TelescopeValues.close_telescope trace
      (by simpa only [List.length_nil, Nat.add_zero, empty] using frame_of_syntax baseline.2.1 baseline.1)
      (by simpa only [List.length_nil, Nat.add_zero, empty] using frame_of_syntax outputFront.2.1 outputFront.1)
      (by simpa only [List.length_nil, Nat.add_zero, empty] using baseline.2.2.1)
      (by simpa only [List.length_nil, Nat.add_zero, empty] using outputFront.2.2.1)
      baseInfer outInfer
      (by simpa only [List.nil_append, Nat.zero_add, len] using leafL)
      (by simpa only [List.nil_append, Nat.zero_add, len] using leafR)
      (by simpa only [List.nil_append, Nat.zero_add, len] using leafEq) markers
  refine ⟨conversion, ?_⟩
  intro φ ρ
  obtain ⟨aa, ba, baseReading, outReading, baseGrade, _, agree⟩ :=
    RuleInputValues.defeq_readings core φ (inputs φ) baseline outputFront conversion
  obtain ⟨_, _, _, pinned, _, _⟩ := targetPackage φ
  have pinEq : ba = core.acval cv.name φ := Option.some.inj (outReading.symm.trans pinned)
  have valueEq : interp V ρ aa = M.model.cval cv.name φ := by
    rw [agree ρ, pinEq, interp_cvalOf core.cval_closedL, publicEq]
  obtain ⟨actual, readBefore, readFinal⟩ := PrefixReadings.inferred_readings_preserved
    core.acval φ target.lookup_preserved (valueFront_frame baseline) baseInfer
  have actualEq : actual = aa := Option.some.inj (readBefore.symm.trans baseReading)
  have finalBaseRead : denoteMeta core.acval envA φ 0 wholeBaseA = some aa :=
    readFinal.trans (congrArg some actualEq)
  have finalRead : denoteMeta M.internal.base2.acval envA φ 0 wholeBaseA = some aa := by
    simpa only [acvalEq] using finalBaseRead
  have baseDenotes := RuleInputValues.reading_denotes M.internal.base2
    (valueFront_frame baseline) finalRead baseGrade ρ
  change Denotes M.model.cval envA φ ρ wholeBaseA (interp V ρ aa) at baseDenotes
  rw [valueEq] at baseDenotes
  exact ⟨baseDenotes, target.denotes M φ ρ⟩

end Ix.CompileCert.O6PrefixValues
