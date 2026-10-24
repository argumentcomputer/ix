import Ix.CompileCert.O6Telescope

/-! # Actual O6 reduction under an arbitrary shared dependent lambda telescope

The real whole checks produce the common typed opening list. Bulk opening
preserves the image's terminal selector body under its own binders, while
its domains may change. Original pass/image/read provenance is retained.
-/

namespace Ix.CompileCert.O6TelescopeOpened

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Model.Rules (Frame)
open O6RecRead O6Annotation O6Telescope

universe w
variable {md : Mode} {env : Ix.Kernel.Env md}

/-- Structural bulk opening returns the actual transformed binder list;
the original terminal body is opened at the cursor below that prefix. -/
theorem strip_open_list {n : Nat} {e tail : Ix.Kernel.Expr md}
    {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : e.stripLams n = some (bs, tail)) (vs : List (Ix.Kernel.Expr md)) (k : Nat) :
    ∃ bs', (e.instantiateList vs k).stripLams n = some (bs', tail.instantiateList vs (k + n)) := by
  induction n generalizing e bs k with
  | zero =>
    have eq : e = tail := (Prod.mk.inj (Option.some.inj strip)).2
    exact ⟨[], by simp only [Ix.Kernel.Expr.stripLams, eq, Nat.add_zero]⟩
  | succ n ih =>
    cases e with
    | lam ty body m =>
      cases rest : body.stripLams n with
      | none => simp only [Ix.Kernel.Expr.stripLams, rest, Option.map_none] at strip; cases strip
      | some pair =>
        simp only [Ix.Kernel.Expr.stripLams, rest, Option.map_some] at strip
        have eq : pair.2 = tail := (Prod.mk.inj (Option.some.inj strip)).2
        have rest' : body.stripLams n = some (pair.1, tail) := eq ▸ rest
        obtain ⟨bs', hs⟩ := ih rest' (k + 1)
        refine ⟨(ty.instantiateList vs k, m) :: bs', ?_⟩
        simp only [Ix.Kernel.Expr.instantiateList, Ix.Kernel.Expr.stripLams, hs,
          Option.map_some, Nat.add_comm, Nat.add_left_comm]
    | _ => cases strip

/-- The functional raw read remains attached to the original source.
Only its actual kernel result is bulk-opened and then annotated. -/
def BulkAnn (keyOf : Ix.Name → Key md) (levelOf : Ix.Level → Ix.Kernel.Level)
    (env : Ix.Kernel.Env md) (d : Nat) (vs : List (Ix.Kernel.Expr md))
    (source : Ix.Expr) (checked : Ix.Kernel.Expr md) : Prop :=
  ∃ raw, Rel (keyOf := keyOf) (levelOf := levelOf) source raw ∧
    Ann env d (raw.instantiateList vs) checked

variable {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

theorem BulkAnn.unique {d : Nat} {vs : List (Ix.Kernel.Expr md)}
    {a b : Ix.Kernel.Expr md} {source : Ix.Expr}
    (ha : BulkAnn keyOf levelOf env d vs source a)
    (hb : BulkAnn keyOf levelOf env d vs source b) : a = b := by
  obtain ⟨ra, hra, aa⟩ := ha
  obtain ⟨rb, hrb, ab⟩ := hb
  have eq := related_unique hra hrb
  subst rb
  exact aa.unique ab

theorem bulk_ann_pairs {d : Nat} {vs : List (Ix.Kernel.Expr md)} {xs : List Ix.Expr}
    {raw checked : List (Ix.Kernel.Expr md)}
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) xs raw)
    (runs : List.Forall₂ (Ann env d) (raw.map (·.instantiateList vs)) checked) :
    List.Forall₂ (BulkAnn keyOf levelOf env d vs) xs checked := by
  induction read generalizing checked with
  | nil => cases runs; exact .nil
  | cons hr ht ih => cases runs with | cons ha rest => exact .cons ⟨_, hr, ha⟩ (ih rest)

theorem bulk_ann_apps {d : Nat} {vs : List (Ix.Kernel.Expr md)} {fk : Ix.Kernel.Expr md} {f : Ix.Expr}
    (hf : BulkAnn keyOf levelOf env d vs f fk) {args : List Ix.Expr} {ks : List (Ix.Kernel.Expr md)}
    (ha : List.Forall₂ (BulkAnn keyOf levelOf env d vs) args ks) :
    BulkAnn keyOf levelOf env d vs (args.foldl Ix.Expr.mkApp f) (fk.mkAppN ks) := by
  induction ha generalizing f fk with
  | nil => exact hf
  | cons ha _ ih =>
    obtain ⟨fr, rf, af⟩ := hf
    obtain ⟨ar, ra, aa⟩ := ha
    exact ih ⟨.app fr ar, .app _ rf ra, by simpa only [Ix.Kernel.Expr.instantiateList] using af.app aa⟩

/-- Actual selection preserves positions and repetitions after bulk opening. -/
theorem selectors_bulk_annotated {d n : Nat} {vs : List (Ix.Kernel.Expr md)}
    {input : Array Ix.Expr} {bs out : List Ix.Expr} {ks args : List (Ix.Kernel.Expr md)}
    (selected : List.Forall₂ (Selects n input) bs out)
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) bs ks)
    (inputAnn : List.Forall₂ (BulkAnn keyOf levelOf env d vs) input.toList args)
    (enough : n ≤ args.length) (closed : ∀ a ∈ args, a.looseBVarsBounded 0 = true) :
    List.Forall₂ (BulkAnn keyOf levelOf env d vs) out
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
/-- The actual O6 layout at the producer's depth. Its Frame and annotation
runs are supplied internally by paired_telescope, not final assumptions. -/
theorem bulk_opened_layout (env : Ix.Kernel.Env md) (d : Nat) (vs : List (Ix.Kernel.Expr md))
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
    (frame : Frame d (baseK.instantiateList vs))
    (baseAnn : annotateCore .verified env FB d (baseK.instantiateList vs) = .ok baseA)
    (outAnn : annotateCore .verified env FO d (outputK.instantiateList vs) = .ok outputA) :
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
  have openBaseEq : baseK.instantiateList vs =
      (imageK.instantiateList vs).mkAppN (argsK.map (·.instantiateList vs)) := by
    rw [baseEq, instantiate_apps]
  obtain ⟨imageA, argsA, ⟨FImage, imageAnn⟩, argRuns, checkedBase⟩ :=
    annotate_apps _ (openBaseEq ▸ baseAnn)
  have closedArgs := annotated_args_closed argRuns (closed_spine _ _ (openBaseEq ▸ frame.2.1)).2
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
  obtain ⟨openBinders, openStrip⟩ := strip_open_list rawStrip vs 0
  simp only [Nat.zero_add, Ix.Kernel.Expr.instantiateList_eq_self bodyFacts.2.2] at openStrip
  obtain ⟨checkedBinders, checkedStrip⟩ := annotate_selector_tail openStrip bodyFacts.1
    (Ix.Kernel.Expr.fvarsBelow_mono (Nat.zero_le d) bodyFacts.2.1) bodyFacts.2.2 imageAnn
  have inputAnn := bulk_ann_pairs argsRel argRuns
  have argumentsOut := selectors_bulk_annotated picked bodyArgsRel inputAnn fit closedArgs
  have more : List.Forall₂ (BulkAnn keyOf levelOf env d vs)
      (o.args.extract s.arity o.args.size).toList (argsA.drop s.arity) := by
    have extraEq : (o.args.extract s.arity o.args.size).toList = o.args.toList.drop s.arity := by
      rw [Array.toList_extract, List.extract_eq_take_drop]
      have len : (o.args.toList.drop s.arity).length = o.args.size - s.arity := by simp
      rw [← len, List.take_length]
    rw [extraEq]
    exact forall₂_drop inputAnn s.arity
  have headAnn : BulkAnn keyOf levelOf env d vs (Ix.Expr.mkConst s.ixRec ls) headK :=
    ⟨headK, headOut, by cases headOut; simp only [Ix.Kernel.Expr.instantiateList]; exact ⟨1, rfl⟩⟩
  have reconstructed : BulkAnn keyOf levelOf env d vs output
      (headK.mkAppN (bodyArgsK.map (·.instantiateList (argsA.take s.arity).reverse) ++ argsA.drop s.arity)) := by
    rw [outputEq]
    simpa only [Ix.Compile.Canon.mkAppN, ← Array.foldl_toList, Array.toList_append] using
      bulk_ann_apps headAnn (Loop.forall₂_append argumentsOut more)
  have outputSame := reconstructed.unique ⟨outputK, outRelated, FO, outAnn⟩
  have fixedHead : headK.instantiateList (argsA.take s.arity).reverse = headK := by
    cases headOut; simp only [Ix.Kernel.Expr.instantiateList]
  refine ⟨imageA, tail, argsA, checkedBinders, checkedBase, checkedStrip, fit, ?_⟩
  simpa only [bodyEq, instantiate_apps, fixedHead, ← apps_append] using outputSame.symm

open Ix.Compile.Pass Ix.Compile.Pass.Opt in
/-- Whole real checks and ordinary root guards derive the common typed
openers, all leaf checks/frames, and O6 Red/DefEq at the telescope's length.
The same domains extend a context for each strong model, without selecting
a satisfying valuation. No whole-lambda value or source/image law is assumed. -/
theorem o6_rec_under_telescope_opened_red (env : Ix.Kernel.Env md)
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
    {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    {wholeBaseA wholeOutA wholeType : Ix.Kernel.Expr md} {FAL FAR FIL : Nat}
    (noFvars : (wrapLams bs baseK).hasFvar = false)
    (bounded : (wrapLams bs baseK).looseBVarsBounded 0 = true)
    (annL : annotateCore .verified env FAL 0 (wrapLams bs baseK) = .ok wholeBaseA)
    (annR : annotateCore .verified env FAR 0 (wrapLams bs outputK) = .ok wholeOutA)
    (inferL : inferTypeCore .verified env FIL 0 wholeBaseA = .ok wholeType) :
    ∃ (As : List (Ix.Kernel.Expr md)) (leftOpen rightOpen innerType : Ix.Kernel.Expr md)
      (fal far fil : Nat),
      DomainTrace env 0 bs As FAL FAR FIL ∧
      FAL = fal + bs.length ∧ FAR = far + bs.length ∧ FIL = fil + bs.length ∧
      annotateCore .verified env fal bs.length
        (baseK.instantiateList (openers 0 As)) = .ok leftOpen ∧
      annotateCore .verified env far bs.length
        (outputK.instantiateList (openers 0 As)) = .ok rightOpen ∧
      inferTypeCore .verified env fil bs.length leftOpen = .ok innerType ∧
      Frame bs.length (baseK.instantiateList (openers 0 As)) ∧ Frame bs.length leftOpen ∧
      Ix.Kernel.Rules.Red env bs.length leftOpen rightOpen ∧
      Ix.Kernel.Rules.DefEq env bs.length leftOpen rightOpen ∧
      ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V env) (φ : LevelParam → Nat),
        ∃ Δ, ContextTrace M.internal.base2 φ 0 [] As Δ ∧ Δ.length = bs.length ∧
          CtxOk M.internal.base2 φ bs.length Δ (baseK.instantiateList (openers 0 As)) ∧
          CtxOk M.internal.base2 φ bs.length Δ leftOpen := by
  obtain ⟨As, left, right, inner, fal, far, fil, trace, eL, eR, eI, aL, aR, iL, rawFr, checkedFr, contexts⟩ :=
    paired_telescope noFvars bounded annL annR inferL
  obtain ⟨imageA, tail, argsA, binders, leftShape, strip, fit, rightShape⟩ :=
    bulk_opened_layout env bs.length (openers 0 As) pass kind blockLookup shapeLookup built source
      generated recognized universeArity baseRead outRead baseRelated outRelated rawFr aL aR
  have reduction : Ix.Kernel.Rules.Red env bs.length left right := by
    rw [leftShape, rightShape]
    exact O6Opened.checked_spine_at strip fit (leftShape ▸ checkedFr) (leftShape ▸ iL)
  exact ⟨As, left, right, inner, fal, far, fil, trace, eL, eR, eI, aL, aR, iL, rawFr, checkedFr,
    reduction, Ix.Kernel.Rules.DefEq.ofRed reduction, contexts⟩

end Ix.CompileCert.O6TelescopeOpened
