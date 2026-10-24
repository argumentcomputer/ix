import Ix.CompileCert.O6Values
import IxC.Kernel.Verify.InferLeaves

/-! # Actual O6 bodies opened by an enclosing lambda

The common typed opener, frames and inner inference come from actual
whole-lambda annotation/inference. Ambient bvar zero is allowed. The result
is body Red/DefEq at depth one, not whole-lambda conversion or public values:
agreement of the two outer markers remains a separate proof obligation.
-/

namespace Ix.CompileCert.O6Opened

open Ix.Kernel
open Ix.Kernel.Model.Rules (Frame)
open Ix.Cert.ConversionValues Ix.Cert.CheckedBetaSpine
open O6RecRead O6Annotation

variable {md : Mode} {env : Ix.Kernel.Env md}

/-- Actual annotation preserves the sole typed opener's leaf identity.
This discharges close-then-reopen; it is not a supplied opening identity. -/
theorem annotation_reopen {rawBody domA opened : Ix.Kernel.Expr md} {F : Nat}
    (noFvars : rawBody.hasFvar = false) (bounded : rawBody.looseBVarsBounded 1 = true)
    (domainFrame : Frame 0 domA)
    (run : annotateCore .verified env F 1
      (rawBody.instantiate1 (.fvar 0 domA)) = .ok opened) :
    (opened.abstract1 0).instantiate1 (.fvar 0 domA) = opened := by
  have rawScope : Ix.Kernel.Expr.WScoped 0 rawBody := .of_not_hasFvar noFvars
  have openedScope := Ix.Kernel.Expr.WScoped.instantiate1 domainFrame.1 0 rawScope
  have openedBound := Ix.Kernel.Expr.looseBVarsBounded_instantiate1_gen
    (a := .fvar 0 domA) rfl bounded
  have leaves := annotateCore_leaves_sub F _ run openedScope openedBound
  have cond : Ix.Kernel.Expr.LeafCond 0 domA opened := by
    intro l hl _
    rcases Ix.Kernel.Expr.fvarLeaves_instantiate1 rawBody 0 (leaves l hl) with old | added
    · rw [Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar noFvars] at old
      cases old
    · have empty := Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar (frame_not_hasFvar domainFrame)
      simp only [Ix.Kernel.Expr.fvarLeaves, empty, List.mem_cons, List.not_mem_nil, or_false] at added
      cases added
      rfl
  exact abstract1_instantiate1 opened 0
    (Ix.Kernel.Expr.fvarConsistent_of_leafCond _ cond)
    (annotateCore_looseBVars F _ run openedBound)

/-- The original inference trace's certified beta argument works at the
actual opening depth as well. Every certificate remains a real run. -/
theorem trace_beta_at {d n : Nat} {head tail type result : Ix.Kernel.Expr md}
    {args : List (Ix.Kernel.Expr md)} {binders : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : head.stripLams n = some (binders, tail))
    (same : Ix.Kernel.Expr.LamPiDomsEq n head type) (fit : n ≤ args.length)
    (trace : ApplicationTrace env d type args result) :
    Ix.Kernel.Rules.Red env d (head.mkAppN args)
      ((tail.instantiateList (args.take n).reverse).mkAppN (args.drop n)) := by
  induction n generalizing head tail type args binders with
  | zero =>
    have eq : head = tail := (Prod.mk.inj (Option.some.inj strip)).2
    simp only [List.take_zero, List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil,
      List.drop_zero, eq]
    exact .refl
  | succ n ih =>
    cases head with
    | lam dom body mb =>
      cases type with
      | forallE dom' cod mt =>
        obtain ⟨rfl, domainTail⟩ := same
        cases restStrip : body.stripLams n with
        | none => simp only [Ix.Kernel.Expr.stripLams, restStrip, Option.map_none] at strip; cases strip
        | some pair =>
          simp only [Ix.Kernel.Expr.stripLams, restStrip, Option.map_some] at strip
          have tailEq : pair.2 = tail := (Prod.mk.inj (Option.some.inj strip)).2
          have bodyStrip : body.stripLams n = some (pair.1, tail) := tailEq ▸ restStrip
          cases args with
          | nil => simp at fit
          | cons arg args =>
            have enough : n ≤ args.length := Nat.le_of_succ_le_succ fit
            cases trace with
            | step headWhnf argRun domainRun traceRest =>
              obtain ⟨rfl, rfl, rfl⟩ := Ix.Kernel.Expr.forallE.inj (whnf_forallE_eq headWhnf)
              have step := Ix.Kernel.Rules.Red.beta (body := body) (mb := mb)
                (Ix.Kernel.Rules.inferTypeCoreIO_bridge (inferTypeCoreIO_of_full argRun))
                (Ix.Kernel.Rules.isDefEqCore_bridge domainRun)
              obtain ⟨nextBinders, nextStrip⟩ := strip_open (v := arg) bodyStrip 0
              simp only [Nat.zero_add] at nextStrip
              have nextDomains := Ix.Kernel.Expr.LamPiDomsEq.instantiate1 (v := arg) n 0 domainTail
              have next := ih nextStrip nextDomains enough traceRest
              have bulk : tail.instantiateList ((arg :: args).take (n + 1)).reverse =
                  (tail.instantiate1 arg n).instantiateList (args.take n).reverse := by
                rw [List.take_succ_cons, List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one]
                simp only [List.length_reverse, List.length_take, Nat.min_eq_left enough, Nat.zero_add]
              rw [bulk, List.drop_succ_cons]
              exact .trans (red_spine step args) next
      | _ => cases same
    | _ => cases strip

theorem checked_spine_at {d n F : Nat} {head tail type : Ix.Kernel.Expr md}
    {args : List (Ix.Kernel.Expr md)} {binders : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : head.stripLams n = some (binders, tail)) (fit : n ≤ args.length)
    (frame : Frame d (head.mkAppN args))
    (run : inferTypeCore .verified env F d (head.mkAppN args) = .ok type) :
    Ix.Kernel.Rules.Red env d (head.mkAppN args)
      ((tail.instantiateList (args.take n).reverse).mkAppN (args.drop n)) := by
  obtain ⟨_, _, headRun, trace⟩ := infer_apps args run
  exact trace_beta_at strip
    (inferred_lam_domains (by rw [strip]; rfl) (frame_head args frame) headRun) fit trace

/-- Raw reading, the specified real kernel opening, then actual annotation. -/
def OpenAnn (keyOf : Ix.Name → Key md) (levelOf : Ix.Level → Ix.Kernel.Level)
    (env : Ix.Kernel.Env md) (d : Nat) (v : Ix.Kernel.Expr md)
    (source : Ix.Expr) (checked : Ix.Kernel.Expr md) : Prop :=
  ∃ raw, Rel (keyOf := keyOf) (levelOf := levelOf) source raw ∧
    Ann env d (raw.instantiate1 v) checked

variable {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

theorem OpenAnn.unique {d : Nat} {v a b : Ix.Kernel.Expr md} {source : Ix.Expr}
    (ha : OpenAnn keyOf levelOf env d v source a)
    (hb : OpenAnn keyOf levelOf env d v source b) : a = b := by
  obtain ⟨ra, hra, aa⟩ := ha
  obtain ⟨rb, hrb, ab⟩ := hb
  have eq := related_unique hra hrb
  subst rb
  exact aa.unique ab

theorem open_ann_pairs {d : Nat} {v : Ix.Kernel.Expr md} {xs : List Ix.Expr}
    {raw checked : List (Ix.Kernel.Expr md)}
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) xs raw)
    (runs : List.Forall₂ (Ann env d) (raw.map (·.instantiate1 v)) checked) :
    List.Forall₂ (OpenAnn keyOf levelOf env d v) xs checked := by
  induction read generalizing checked with
  | nil => cases runs; exact .nil
  | cons hr ht ih => cases runs with | cons ha rest => exact .cons ⟨_, hr, ha⟩ (ih rest)

theorem open_ann_apps {d : Nat} {v fk : Ix.Kernel.Expr md} {f : Ix.Expr}
    (hf : OpenAnn keyOf levelOf env d v f fk) {args : List Ix.Expr} {ks : List (Ix.Kernel.Expr md)}
    (ha : List.Forall₂ (OpenAnn keyOf levelOf env d v) args ks) :
    OpenAnn keyOf levelOf env d v (args.foldl Ix.Expr.mkApp f) (fk.mkAppN ks) := by
  induction ha generalizing f fk with
  | nil => exact hf
  | cons ha _ ih =>
    obtain ⟨fr, rf, af⟩ := hf
    obtain ⟨ar, ra, aa⟩ := ha
    exact ih ⟨.app fr ar, .app _ rf ra, af.app aa⟩

/-- Selection remains positional after the actual common opening. -/
theorem selectors_open_annotated {d n : Nat} {v : Ix.Kernel.Expr md}
    {input : Array Ix.Expr} {bs out : List Ix.Expr} {ks args : List (Ix.Kernel.Expr md)}
    (selected : List.Forall₂ (Selects n input) bs out)
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) bs ks)
    (inputAnn : List.Forall₂ (OpenAnn keyOf levelOf env d v) input.toList args)
    (enough : n ≤ args.length) (closed : ∀ a ∈ args, a.looseBVarsBounded 0 = true) :
    List.Forall₂ (OpenAnn keyOf levelOf env d v) out
      (ks.map (·.instantiateList (args.take n).reverse)) := by
  induction selected generalizing ks with
  | nil => cases read; exact .nil
  | cons head rest ih =>
    cases read with
    | cons hb ht =>
      obtain ⟨i, hash, bound, rfl, found⟩ := head
      cases hb
      obtain ⟨arg, atArg, related⟩ := SourceConstructorPositions.forall₂_getElem? inputAnn
        (i := i) (by simpa only [Array.getElem?_toList] using found)
      have atTake : (args.take n)[i]? = some arg := by rwa [List.getElem?_take_of_lt bound]
      have eq := instantiate_bvar_lookup (n := n) (by simp [Nat.min_eq_left enough]) atTake
        (fun x hx => closed x (List.mem_of_mem_take hx))
      exact .cons (by simpa only [Ix.Kernel.Expr.mkBvar_eq, eq] using related) (ih ht)

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- The real O6 selector layout after one common typed opening. The ambient
bvar is permitted; the terminal body is fixed by its derived selector bound,
while image domains may change. This helper's opening/annotation inputs are
derived from whole-lambda runs by the public endpoint below. -/
theorem opened_layout (env : Ix.Kernel.Env md) (domA : Ix.Kernel.Expr md)
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
    {baseK outputK baseA outputA : Ix.Kernel.Expr md} {FB FO : Nat}
    (_baseRead : baseReader.read baseWire = .ok baseK) (_outRead : outReader.read outWire = .ok outputK)
    (baseRelated : Rel (keyOf := keyOf) (levelOf := levelOf)
      (Ix.Compile.Canon.mkAppN (Ix.Compile.Canon.substLevels img.levelParams o.us img.value) o.args) baseK)
    (outRelated : Rel (keyOf := keyOf) (levelOf := levelOf) output outputK)
    (bounded : baseK.looseBVarsBounded 1 = true)
    (baseAnn : annotateCore .verified env FB 1 (baseK.instantiate1 (.fvar 0 domA)) = .ok baseA)
    (outAnn : annotateCore .verified env FO 1 (outputK.instantiate1 (.fvar 0 domA)) = .ok outputA) :
    ∃ (imageA tail : Ix.Kernel.Expr md) (argsA : List (Ix.Kernel.Expr md))
      (binders : List (Ix.Kernel.Expr md × BinderMeta)),
      baseA = imageA.mkAppN argsA ∧ imageA.stripLams s.arity = some (binders, tail) ∧
      s.arity ≤ argsA.length ∧
      outputA = (tail.instantiateList (argsA.take s.arity).reverse).mkAppN (argsA.drop s.arity) := by
  obtain ⟨ls, ms, mins, selected, enough, levelsRun, pickM, pickN, outputEq⟩ :=
    o6_rec_output pass kind blockLookup shapeLookup
  obtain ⟨_, _, _, body, bs, iv, hash, _, _, _, _, _, _, _, data, _⟩ :=
    ImageShape.production_origin built source generated recognized
  have params : s.levelParams = img.levelParams := (ImageShape.readShape_result recognized).2.1
  have picked := data_picks data selected enough pickM pickN
  have noLevels := selects_subst picked img.levelParams o.us
  have readBase : Rel (keyOf := keyOf) (levelOf := levelOf)
      (o.args.toList.foldl Ix.Expr.mkApp (Ix.Compile.Canon.substLevels img.levelParams o.us img.value)) baseK := by
    simpa only [Ix.Compile.Canon.mkAppN, Array.foldl_toList] using baseRelated
  obtain ⟨imageK, argsK, imageRel, argsRel, baseEq⟩ := related_apps_inv o.args.toList readBase
  have openBaseEq : baseK.instantiate1 (.fvar 0 domA) =
      (imageK.instantiate1 (.fvar 0 domA)).mkAppN (argsK.map (·.instantiate1 (.fvar 0 domA))) := by
    rw [baseEq, Ix.Kernel.Expr.mkAppN_instantiate1]
  obtain ⟨imageA, argsA, ⟨FImage, imageAnn⟩, argRuns, checkedBase⟩ :=
    annotate_apps _ (openBaseEq ▸ baseAnn)
  have openBound := Ix.Kernel.Expr.looseBVarsBounded_instantiate1_gen
    (a := .fvar 0 domA) rfl bounded
  have closedRaw := (closed_spine _ _ (openBaseEq ▸ openBound)).2
  have closedArgs := annotated_args_closed argRuns closedRaw
  have fit : s.arity ≤ argsA.length := by
    have rawSize := CliqueRowsCoverage.forall₂_lengths argsRel
    have annSize := CliqueRowsCoverage.forall₂_lengths argRuns
    simp only [Array.length_toList] at rawSize
    simp only [List.length_map] at annSize
    omega
  obtain ⟨tail, chain, bodyRel⟩ := related_stripLams imageRel (strip_subst img.levelParams o.us data.1)
  obtain ⟨headK, bodyArgsK, headRel, bodyArgsRel, bodyEq⟩ := related_getApps bodyRel
  simp only [app_spine_subst, data.2.1, noLevels] at headRel bodyArgsRel
  have instantiatedLevels :
      (if img.levelParams.isEmpty || o.us.isEmpty then s.ixLevels
        else s.ixLevels.map (Ix.Compile.Canon.substLevel img.levelParams o.us)) = ls := by
    rw [← params]
    exact o5_subst_levels (by rwa [params]) levelsRun
  have headOut := subst_const_related headRel instantiatedLevels
  have bodyFacts : Flat tail ∧ tail.fvarsBelow 0 ∧ tail.looseBVarsBounded s.arity = true := by
    rw [bodyEq]
    exact spine_facts bodyArgsK (by cases headOut; exact ⟨.const _ _, trivial, rfl⟩)
      (selectors_facts picked bodyArgsRel)
  obtain ⟨rawBinders, rawStrip⟩ := raw_prefix_strip chain
  obtain ⟨openBinders, openStrip⟩ := strip_open (v := .fvar 0 domA) rawStrip 0
  simp only [Nat.zero_add, Ix.Kernel.Expr.instantiate1_eq_self bodyFacts.2.2] at openStrip
  obtain ⟨checkedBinders, checkedStrip⟩ := annotate_selector_tail openStrip bodyFacts.1
    (Ix.Kernel.Expr.fvarsBelow_mono (by omega : 0 ≤ 1) bodyFacts.2.1) bodyFacts.2.2 imageAnn
  have inputAnn := open_ann_pairs argsRel argRuns
  have argumentsOut := selectors_open_annotated picked bodyArgsRel inputAnn fit closedArgs
  have more : List.Forall₂ (OpenAnn keyOf levelOf env 1 (.fvar 0 domA))
      (o.args.extract s.arity o.args.size).toList (argsA.drop s.arity) := by
    have extraEq : (o.args.extract s.arity o.args.size).toList = o.args.toList.drop s.arity := by
      rw [Array.toList_extract, List.extract_eq_take_drop]
      have len : (o.args.toList.drop s.arity).length = o.args.size - s.arity := by simp
      rw [← len, List.take_length]
    rw [extraEq]
    exact forall₂_drop inputAnn s.arity
  have headAnn : OpenAnn keyOf levelOf env 1 (.fvar 0 domA) (Ix.Expr.mkConst s.ixRec ls) headK :=
    ⟨headK, headOut, by cases headOut; exact ⟨1, rfl⟩⟩
  have reconstructed : OpenAnn keyOf levelOf env 1 (.fvar 0 domA) output
      (headK.mkAppN (bodyArgsK.map (·.instantiateList (argsA.take s.arity).reverse) ++ argsA.drop s.arity)) := by
    rw [outputEq]
    simpa only [Ix.Compile.Canon.mkAppN, ← Array.foldl_toList, Array.toList_append] using
      open_ann_apps headAnn (Loop.forall₂_append argumentsOut more)
  have outputSame := reconstructed.unique ⟨outputK, outRelated, FO, outAnn⟩
  have fixedHead : headK.instantiateList (argsA.take s.arity).reverse = headK := by
    cases headOut; simp only [Ix.Kernel.Expr.instantiateList]
  refine ⟨imageA, tail, argsA, checkedBinders, checkedBase, checkedStrip, fit, ?_⟩
  simpa only [bodyEq, instantiate_apps, fixedHead, ← apps_append] using outputSame.symm

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- One actual enclosing lambda supplies the common typed opener and all
inner runs. The body may use the ambient bvar zero. Body Red/DefEq at depth
one is derived, including Prop; no opening/frame/layout/conversion premise
or output inference is supplied. The outer markers are retained separately:
their agreement and whole-lambda public values remain unproved here.

All pass/image/read provenance and the exact prefix env remain explicit.
This local context step does not claim a Translate.rw fold, .recOn,
fallback, source/image N-PERM or the final all-rewrites theorem. -/
theorem o6_rec_under_lam_opened_red (env : Ix.Kernel.Env md)
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
    {rawDom wholeBaseA wholeOutA wholeType : Ix.Kernel.Expr md} {rawMeta : BinderMeta}
    {FB FO FI : Nat}
    (noFvars : (Ix.Kernel.Expr.lam rawDom baseK rawMeta).hasFvar = false)
    (bounded : (Ix.Kernel.Expr.lam rawDom baseK rawMeta).looseBVarsBounded 0 = true)
    (baseAnn : annotateCore .verified env FB 0 (.lam rawDom baseK rawMeta) = .ok wholeBaseA)
    (outAnn : annotateCore .verified env FO 0 (.lam rawDom outputK rawMeta) = .ok wholeOutA)
    (baseInfer : inferTypeCore .verified env FI 0 wholeBaseA = .ok wholeType) :
    ∃ (domA leftOpen rightOpen innerType : Ix.Kernel.Expr md)
      (pwL pwR : PropWhen) (fB fO fI : Nat),
      FB = fB + 1 ∧ FO = fO + 1 ∧ FI = fI + 1 ∧
      annotateCore .verified env fB 0 rawDom = .ok domA ∧
      annotateCore .verified env fO 0 rawDom = .ok domA ∧
      annotateCore .verified env fB 1 (baseK.instantiate1 (.fvar 0 domA)) = .ok leftOpen ∧
      annotateCore .verified env fO 1 (outputK.instantiate1 (.fvar 0 domA)) = .ok rightOpen ∧
      (if !pwWritten rawMeta.pw then annotPwLam (pureFns .verified env fB) env 1 leftOpen
        else pure rawMeta.pw) = .ok pwL ∧
      (if !pwWritten rawMeta.pw then annotPwLam (pureFns .verified env fO) env 1 rightOpen
        else pure rawMeta.pw) = .ok pwR ∧
      wholeBaseA = .lam domA (leftOpen.abstract1 0) {rawMeta with pw := pwL} ∧
      wholeOutA = .lam domA (rightOpen.abstract1 0) {rawMeta with pw := pwR} ∧
      Frame 0 domA ∧ Frame 1 leftOpen ∧
      (leftOpen.abstract1 0).instantiate1 (.fvar 0 domA) = leftOpen ∧
      inferTypeCore .verified env fI 1 leftOpen = .ok innerType ∧
      Ix.Kernel.Rules.Red env 1 leftOpen rightOpen ∧
      Ix.Kernel.Rules.DefEq env 1 leftOpen rightOpen := by
  cases FB with
  | zero => rw [annotateCore_zero] at baseAnn; exact nomatch baseAnn
  | succ fB =>
  cases FO with
  | zero => rw [annotateCore_zero] at outAnn; exact nomatch outAnn
  | succ fO =>
  cases FI with
  | zero => rw [inferTypeCore_zero] at baseInfer; exact nomatch baseInfer
  | succ fI =>
  obtain ⟨domA, leftOpen, pwL, domRunL, leftAnn, markerL, baseShape⟩ :=
    Ix.Cert.AnnotatedBeta.annotate_lam_trace baseAnn
  obtain ⟨domOut, rightOpen, pwR, domRunR, rightAnn, markerR, outShape⟩ :=
    Ix.Cert.AnnotatedBeta.annotate_lam_trace outAnn
  have common := annotation_unique domRunL domRunR
  subst domOut
  have rawNo := noFvars
  have rawBound := bounded
  simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at rawNo
  simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at rawBound
  have domainFrame := annotation_frame domRunL rawNo.1 rawBound.1
  have reopen := annotation_reopen rawNo.2 rawBound.2 domainFrame leftAnn
  have wholeFrame := annotation_frame baseAnn noFvars bounded
  rw [baseShape] at wholeFrame
  have innerFrame := wholeFrame.lam_open domainFrame
  rw [reopen] at innerFrame
  have inferred := baseInfer
  rw [baseShape] at inferred
  obtain ⟨_, _, innerType, _, _, innerInfer, _, _, _⟩ := inferTypeCore_lam_inv inferred
  rw [reopen] at innerInfer
  obtain ⟨imageA, tail, argsA, binders, leftShape, strip, fit, rightShape⟩ :=
    opened_layout env domA pass kind blockLookup shapeLookup built source generated
      recognized universeArity baseRead outRead baseRelated outRelated rawBound.2 leftAnn rightAnn
  have reduction : Ix.Kernel.Rules.Red env 1 leftOpen rightOpen := by
    rw [leftShape, rightShape]
    exact checked_spine_at strip fit (leftShape ▸ innerFrame) (leftShape ▸ innerInfer)
  exact ⟨domA, leftOpen, rightOpen, innerType, pwL, pwR, fB, fO, fI,
    rfl, rfl, rfl, domRunL, domRunR, leftAnn, rightAnn, markerL, markerR,
    baseShape, outShape, domainFrame, innerFrame, reopen, innerInfer,
    reduction, Ix.Kernel.Rules.DefEq.ofRed reduction⟩

end Ix.CompileCert.O6Opened
