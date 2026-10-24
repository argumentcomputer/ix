import Ix.CompileCert.O6TelescopeOpened
import Ix.Cert.LambdaMarkers
import IxC.Kernel.Verify.PropRead

/-! # Closing actual paired lambda telescopes

Both actual full-inference chains propagate the marker compatibility
derived from real root fronts inside each supplied strong model. The
produced DomainTrace and terminal comparison then close the whole prefix.
No inference against a newly invented inner expected type is required.
-/

namespace Ix.CompileCert.O6TelescopeValues

open Ix.Kernel Ix.Kernel.Semantics
open Ix.Kernel.Model.Rules (Frame)
open Ix.Cert.ConversionValues
open O6RecRead O6Annotation O6Telescope

universe w
variable {md : Mode} {env : Ix.Kernel.Env md}

/-- Re-abstraction preserves an existing lambda's marker and never creates
a lambda at a non-lambda root. -/
theorem lamPw_abstract1 (e : Ix.Kernel.Expr md) (d k : Nat) :
    (e.abstract1 d k).lamPw = e.lamPw := by
  cases e with
  | fvar idx ty =>
    by_cases h : idx = d <;> simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw, h]
  | _ => rfl

/-- Root compatibility is derived within each supplied model from the
actual header and both value fronts. Non-lambda roots need no marker. -/
theorem markers_of_fronts {V : Type w} [SetTheory V] (M : Cached.StrongModel V env)
    {cv : Ix.Kernel.ConstantVal md}
    {expected headerSortType rawL rawR checkedL checkedR : Ix.Kernel.Expr md}
    {FA FT FL FR : Nat}
    (headerClosed : cv.type.hasFvar = false)
    (headerBounded : cv.type.looseBVarsBounded 0 = true)
    (headerAnn : annotateCore .verified env FA 0 cv.type = .ok expected)
    (headerInfer : inferTypeCore .verified env FT 0 expected = .ok headerSortType)
    (left : ValueFrontRun .verified FL env cv rawL expected checkedL)
    (right : ValueFrontRun .verified FR env cv rawR expected checkedR) :
    ∀ p q, checkedL.lamPw = some p → checkedR.lamPw = some q → p = q := by
  intro p q hp hq
  obtain ⟨_, _, _, rfl, rfl⟩ := Ix.Kernel.Expr.lamPw_some_inv hp
  obtain ⟨_, _, _, rfl, rfl⟩ := Ix.Kernel.Expr.lamPw_some_inv hq
  exact Ix.Cert.LambdaMarkers.lambda_markers_eq_of_fronts M
    headerClosed headerBounded headerAnn headerInfer left right

/-- Internal closing adapter. Its trace, terminal calls/comparison and root
marker compatibility are produced by the public theorem. Every recursive
run is extracted from the supplied whole runs; both reopening identities
are proved from the actual raw frames. No inner header check is assumed. -/
theorem close_telescope {d FAL FAR FIL FIR FL FR : Nat}
    {prior As : List (Ix.Kernel.Expr md)} {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    {base output checkedL checkedR typeL typeR leftOpen rightOpen : Ix.Kernel.Expr md}
    (trace : DomainTraceFrom env d prior bs As FAL FAR FIL)
    (frameL : Frame (d + prior.length) ((wrapLams bs base).instantiateList (openers d prior)))
    (frameR : Frame (d + prior.length) ((wrapLams bs output).instantiateList (openers d prior)))
    (annL : annotateCore .verified env FAL (d + prior.length)
      ((wrapLams bs base).instantiateList (openers d prior)) = .ok checkedL)
    (annR : annotateCore .verified env FAR (d + prior.length)
      ((wrapLams bs output).instantiateList (openers d prior)) = .ok checkedR)
    (inferL : inferTypeCore .verified env FIL (d + prior.length) checkedL = .ok typeL)
    (inferR : inferTypeCore .verified env FIR (d + prior.length) checkedR = .ok typeR)
    (leafL : annotateCore .verified env FL (d + (prior ++ As).length)
      (base.instantiateList (openers d (prior ++ As))) = .ok leftOpen)
    (leafR : annotateCore .verified env FR (d + (prior ++ As).length)
      (output.instantiateList (openers d (prior ++ As))) = .ok rightOpen)
    (leafEq : Ix.Kernel.Rules.DefEq env (d + (prior ++ As).length) leftOpen rightOpen)
    (markers : ∀ p q, checkedL.lamPw = some p → checkedR.lamPw = some q → p = q) :
    Ix.Kernel.Rules.DefEq env (d + prior.length) checkedL checkedR := by
  induction trace generalizing checkedL checkedR typeL typeR FIR with
  | nil =>
    simp only [wrapLams_nil, List.append_nil] at annL annR leafL leafR leafEq
    have leftEq := annotation_unique annL leafL
    have rightEq := annotation_unique annR leafR
    rwa [← leftEq, ← rightEq] at leafEq
  | @step prior bs As rawTy rawMeta A AT u fal far fil domainFrame domainL domainR
      domainInfer domainSort rest ih =>
    simp only [wrapLams_cons, Ix.Kernel.Expr.instantiateList] at frameL frameR annL annR
    obtain ⟨AL, left, pwL, domainL', bodyL, shapeL⟩ := annotateCore_lam_inv annL
    obtain ⟨AR, right, pwR, domainR', bodyR, shapeR⟩ := annotateCore_lam_inv annR
    have commonL := annotation_unique domainL domainL'
    have commonR := annotation_unique domainR domainR'
    subst AL
    subst AR
    have scopeL := frameL.1
    have scopeR := frameR.1
    have boundL := frameL.2.1
    have boundR := frameR.2.1
    simp only [Ix.Kernel.Expr.WScoped] at scopeL scopeR
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at boundL boundR
    have reopenL := annotation_reopen_at scopeL.2 boundL.2 domainFrame bodyL
    have reopenR := annotation_reopen_at scopeR.2 boundR.2 domainFrame bodyR
    rw [shapeL] at inferL
    rw [shapeR] at inferR
    cases FIR with
    | zero => rw [inferTypeCore_zero] at inferR; exact nomatch inferR
    | succ fir =>
    obtain ⟨_, _, innerL, _, _, bodyInferL, _, inheritL, _⟩ := inferTypeCore_lam_inv inferL
    obtain ⟨_, _, innerR, _, _, bodyInferR, _, inheritR, _⟩ := inferTypeCore_lam_inv inferR
    rw [reopenL] at bodyInferL
    rw [reopenR] at bodyInferR
    have sameMarkers : pwL = pwR := markers pwL pwR
      (by rw [shapeL]; rfl) (by rw [shapeR]; rfl)
    have childMarkers : ∀ p q, left.lamPw = some p → right.lamPw = some q → p = q := by
      intro p q hp hq
      have copyL := inheritL rfl p (by simpa only [lamPw_abstract1] using hp)
      have copyR := inheritR rfl q (by simpa only [lamPw_abstract1] using hq)
      exact copyL.symm.trans (sameMarkers.trans copyR)
    have depth : d + (prior ++ [A]).length = d + prior.length + 1 := by simp [Nat.add_assoc]
    have appendEq : (prior ++ [A]) ++ As = prior ++ A :: As := by
      simp only [List.append_assoc, List.singleton_append]
    have nextFrameL : Frame (d + (prior ++ [A]).length)
        ((wrapLams bs base).instantiateList (openers d (prior ++ [A]))) := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using
        frameL.lam_open domainFrame
    have nextFrameR : Frame (d + (prior ++ [A]).length)
        ((wrapLams bs output).instantiateList (openers d (prior ++ [A]))) := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using
        frameR.lam_open domainFrame
    have nextL : annotateCore .verified env fal (d + (prior ++ [A]).length)
        ((wrapLams bs base).instantiateList (openers d (prior ++ [A]))) = .ok left := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using bodyL
    have nextR : annotateCore .verified env far (d + (prior ++ [A]).length)
        ((wrapLams bs output).instantiateList (openers d (prior ++ [A]))) = .ok right := by
      simpa only [depth, openers_append_one, Ix.Kernel.Expr.instantiateList_cons] using bodyR
    have inner := ih nextFrameL nextFrameR nextL nextR (depth.symm ▸ bodyInferL)
      (depth.symm ▸ bodyInferR) (appendEq.symm ▸ leafL) (appendEq.symm ▸ leafR)
      (appendEq.symm ▸ leafEq) childMarkers
    rw [shapeL, shapeR]
    refine .lam .refl ?_ sameMarkers rfl
    simpa only [reopenL, reopenR] using (depth ▸ inner)

variable {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- Arbitrary shared dependent lambda telescopes preserve their whole
checked values at every supplied strong model. SourceFormInfers and target
admission must supply BOTH actual value fronts against this same header
in this exact prefix env; ordinary source acceptance does not supply the
baseline front here. All opening/leaf/marker premises are derived below. -/
theorem o6_rec_under_telescope_values (env : Ix.Kernel.Env md)
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
    {cv : Ix.Kernel.ConstantVal md} {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    {expected headerSortType wholeBaseA wholeOutA : Ix.Kernel.Expr md} {FA FT FB FO : Nat}
    (headerClosed : cv.type.hasFvar = false)
    (headerBounded : cv.type.looseBVarsBounded 0 = true)
    (headerAnn : annotateCore .verified env FA 0 cv.type = .ok expected)
    (headerInfer : inferTypeCore .verified env FT 0 expected = .ok headerSortType)
    (baseFront : ValueFrontRun .verified FB env cv (wrapLams bs baseK) expected wholeBaseA)
    (outFront : ValueFrontRun .verified FO env cv (wrapLams bs outputK) expected wholeOutA) :
    ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env),
      Ix.Kernel.Rules.DefEq env 0 wholeBaseA wholeOutA ∧
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        ∃ value, Denotes M.model.cval env φ ρ wholeBaseA value ∧
          Denotes M.model.cval env φ ρ wholeOutA value := by
  obtain ⟨_, baseInfer, _⟩ := baseFront.2.2.2.2.2
  obtain ⟨_, outInfer, _⟩ := outFront.2.2.2.2.2
  obtain ⟨As, _, _, _, _, _, _, trace, _, _, _, leafL, leafR, _, _, _, _, leafEq, _⟩ :=
    O6TelescopeOpened.o6_rec_under_telescope_opened_red.{w} env pass kind blockLookup shapeLookup
      built source generated recognized universeArity baseRead outRead baseRelated outRelated
      baseFront.2.1 baseFront.1 baseFront.2.2.1 outFront.2.2.1 baseInfer
  have len := DomainTrace.length trace
  have empty (e : Ix.Kernel.Expr md) : e.instantiateList (openers 0 []) = e := by
    simp only [openers, List.zipIdx_nil, List.map_nil, List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil]
  intro V _ M
  have markers := markers_of_fronts M headerClosed headerBounded headerAnn headerInfer baseFront outFront
  have conversion : Ix.Kernel.Rules.DefEq env 0 wholeBaseA wholeOutA := close_telescope trace
    (by simpa only [List.length_nil, Nat.add_zero, empty] using frame_of_syntax baseFront.2.1 baseFront.1)
    (by simpa only [List.length_nil, Nat.add_zero, empty] using frame_of_syntax outFront.2.1 outFront.1)
    (by simpa only [List.length_nil, Nat.add_zero, empty] using baseFront.2.2.1)
    (by simpa only [List.length_nil, Nat.add_zero, empty] using outFront.2.2.1)
    baseInfer outInfer
    (by simpa only [List.nil_append, Nat.zero_add, len] using leafL)
    (by simpa only [List.nil_append, Nat.zero_add, len] using leafR)
    (by simpa only [List.nil_append, Nat.zero_add, len] using leafEq) markers
  exact ⟨conversion, fun φ ρ => valueFront_defeq_values M baseFront outFront conversion φ ρ⟩

end Ix.CompileCert.O6TelescopeValues
