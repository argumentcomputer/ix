import Ix.CompileCert.O6RecRead
import Ix.Cert.AnnotatedBeta
import IxC.Kernel.Verify.Subst

/-! # Actual O6 selector annotation layout

Successful annotations are compared at one environment and depth, using
fuel monotonicity. The image's terminal selector spine survives its actual
typed openings and re-abstractions; domains and binder markers may change.
This is a structural bridge only. Certified beta spines, public values,
under-binder occurrences and fallback development remain separate proofs.
-/

namespace Ix.CompileCert.O6Annotation

open Ix.Kernel
open O6RecRead

variable {md : Mode} {env : Ix.Kernel.Env md}

/-- A successful real annotation, with its own fuel retained existentially. -/
def Ann (env : Ix.Kernel.Env md) (d : Nat) (raw checked : Ix.Kernel.Expr md) : Prop :=
  ∃ F, annotateCore .verified env F d raw = .ok checked

theorem annotation_unique {F G d : Nat} {raw a b : Ix.Kernel.Expr md}
    (ha : annotateCore .verified env F d raw = .ok a)
    (hb : annotateCore .verified env G d raw = .ok b) : a = b :=
  Except.ok.inj ((annotateCore_mono (Nat.le_max_left F G) ha).symm.trans
    (annotateCore_mono (Nat.le_max_right F G) hb))

theorem Ann.unique {d : Nat} {raw a b : Ix.Kernel.Expr md}
    (ha : Ann env d raw a) (hb : Ann env d raw b) : a = b := by
  obtain ⟨F, ha⟩ := ha
  obtain ⟨G, hb⟩ := hb
  exact annotation_unique ha hb

theorem Ann.app {d : Nat} {f a f' a' : Ix.Kernel.Expr md}
    (hf : Ann env d f f') (ha : Ann env d a a') : Ann env d (.app f a) (.app f' a') := by
  obtain ⟨F, hf⟩ := hf
  obtain ⟨G, ha⟩ := ha
  refine ⟨max F G + 1, ?_⟩
  rw [annotateCore_succ]
  simp only [annotateBody, annotate_def, annotateCore_mono (Nat.le_max_left F G) hf,
    annotateCore_mono (Nat.le_max_right F G) ha, Bind.bind, Except.bind, pure, Except.pure]

/-- Every subterm witness is extracted from this actual application run. -/
theorem annotate_apps {d F : Nat} (args : List (Ix.Kernel.Expr md))
    {head checked : Ix.Kernel.Expr md}
    (run : annotateCore .verified env F d (head.mkAppN args) = .ok checked) :
    ∃ headA argsA, Ann env d head headA ∧ List.Forall₂ (Ann env d) args argsA ∧
      checked = headA.mkAppN argsA := by
  induction args generalizing head checked with
  | nil => exact ⟨checked, [], ⟨F, run⟩, .nil, rfl⟩
  | cons a args ih =>
    obtain ⟨fa, argsA, ⟨G, headRun⟩, rest, shape⟩ := ih run
    cases G with
    | zero => rw [annotateCore_zero] at headRun; exact nomatch headRun
    | succ G =>
      obtain ⟨headA, aA, hf, ha, rfl⟩ := annotateCore_app_inv headRun
      exact ⟨headA, aA :: argsA, ⟨G, hf⟩, .cons ⟨G, ha⟩ rest, shape⟩

/-- Only selector syntax, with typed free variables treated as opaque leaves. -/
inductive Flat : Ix.Kernel.Expr md → Prop
  | bvar (i) : Flat (.bvar i)
  | fvar (i ty) : Flat (.fvar i ty)
  | const (k us) : Flat (.const k us)
  | app {f a} : Flat f → Flat a → Flat (.app f a)

theorem Flat.annotate {e : Ix.Kernel.Expr md} (flat : Flat e)
    {F d : Nat} {checked : Ix.Kernel.Expr md}
    (run : annotateCore .verified env F d e = .ok checked) : checked = e := by
  induction flat generalizing F d checked with
  | bvar i | const k us =>
    cases F with
    | zero => rw [annotateCore_zero] at run; exact nomatch run
    | succ F =>
      simpa only [annotateCore_succ, annotateBody, pure, Except.pure, Except.ok.injEq] using run.symm
  | fvar i ty =>
    cases F with
    | zero => rw [annotateCore_zero] at run; exact nomatch run
    | succ F =>
      rw [annotateCore_succ] at run
      simp only [annotateBody] at run
      split at run
      · exact (Except.ok.inj run).symm
      · exact nomatch run
  | app hf ha ihf iha =>
    cases F with
    | zero => rw [annotateCore_zero] at run; exact nomatch run
    | succ F =>
      obtain ⟨f', a', rf, ra, rfl⟩ := annotateCore_app_inv run
      rw [ihf rf, iha ra]

theorem Flat.open {e : Ix.Kernel.Expr md} (flat : Flat e) (d k : Nat) (ty : Ix.Kernel.Expr md) :
    Flat (e.instantiate1 (.fvar d ty) k) := by
  induction flat with
  | bvar i => simp only [Ix.Kernel.Expr.instantiate1]; split <;> try exact .fvar _ _
              split <;> exact .bvar _
  | fvar => exact .fvar _ _
  | const => exact .const _ _
  | app _ _ ihf iha => exact .app ihf iha

/-- Fresh open-then-close, with the bound needed because abstract1 does not
raise unrelated bvars. This is syntax, not annotation transparency. -/
theorem open_close (e : Ix.Kernel.Expr md) (d k : Nat) (ty : Ix.Kernel.Expr md)
    (fresh : e.fvarsBelow d) (bounded : e.looseBVarsBounded (k + 1) = true) :
    (e.instantiate1 (.fvar d ty) k).abstract1 d k = e := by
  induction e generalizing k with
  | bvar i =>
    have bound : i < k + 1 := by simpa only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] using bounded
    by_cases eq : i = k
    · simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.abstract1, eq]
    · have below : ¬i > k := by omega
      simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.abstract1, eq, below]
  | fvar i t _ =>
    have ne : i ≠ d := by change i < d at fresh; omega
    simp only [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.abstract1, ne, ↓reduceIte]
  | _ => simp_all [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.abstract1,
      Ix.Kernel.Expr.fvarsBelow, Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true]

theorem strip_open {n : Nat} {e tail v : Ix.Kernel.Expr md}
    {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : e.stripLams n = some (bs, tail)) (k : Nat) :
    ∃ bs', (e.instantiate1 v k).stripLams n = some (bs', tail.instantiate1 v (k + n)) := by
  have someRun := Ix.Kernel.Expr.stripLams_instantiate1_isSome (v := v) n k (by rw [strip]; rfl)
  cases run : (e.instantiate1 v k).stripLams n with
  | none => rw [run] at someRun; cases someRun
  | some pair =>
    obtain ⟨bs', tail'⟩ := pair
    have eq := (Ix.Kernel.Expr.stripLams_instantiate1_eq n k strip run).1
    exact ⟨bs', by rw [eq]⟩

theorem strip_abstract {n : Nat} {e tail : Ix.Kernel.Expr md}
    {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : e.stripLams n = some (bs, tail)) (d k : Nat) :
    ∃ bs', (e.abstract1 d k).stripLams n = some (bs', tail.abstract1 d (k + n)) := by
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
        refine ⟨(ty.abstract1 d k, m) :: bs', ?_⟩
        simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.stripLams, hs,
          Option.map_some, Nat.add_comm, Nat.add_left_comm]
    | _ => cases strip

/-- The actual typed opener and re-abstraction preserve the exact terminal
selector body. No constraint is put on changed domains or marker values. -/
theorem annotate_selector_tail {n F d : Nat} {image tail checked : Ix.Kernel.Expr md}
    {bs : List (Ix.Kernel.Expr md × BinderMeta)}
    (strip : image.stripLams n = some (bs, tail)) (flat : Flat tail)
    (fresh : tail.fvarsBelow d) (bounded : tail.looseBVarsBounded n = true)
    (run : annotateCore .verified env F d image = .ok checked) :
    ∃ bsA, checked.stripLams n = some (bsA, tail) := by
  induction n generalizing image bs checked F d tail with
  | zero =>
    have eq : image = tail := (Prod.mk.inj (Option.some.inj strip)).2
    subst image
    exact ⟨[], by rw [flat.annotate run]; rfl⟩
  | succ n ih =>
    cases image with
    | lam ty body m =>
      cases rest : body.stripLams n with
      | none => simp only [Ix.Kernel.Expr.stripLams, rest, Option.map_none] at strip; cases strip
      | some pair =>
        simp only [Ix.Kernel.Expr.stripLams, rest, Option.map_some] at strip
        have eq : pair.2 = tail := (Prod.mk.inj (Option.some.inj strip)).2
        have rest : body.stripLams n = some (pair.1, tail) := eq ▸ rest
        cases F with
        | zero => rw [annotateCore_zero] at run; exact nomatch run
        | succ F =>
          obtain ⟨tyA, openedA, pw, _, bodyRun, rfl⟩ := annotateCore_lam_inv run
          obtain ⟨bsO, opened⟩ := strip_open (v := .fvar d tyA) rest 0
          simp only [Nat.zero_add] at opened
          obtain ⟨bsA, annotated⟩ := ih opened (flat.open d n tyA)
            (Ix.Kernel.Expr.fvarsBelow_instantiate1 n fresh)
            (Ix.Kernel.Expr.looseBVarsBounded_instantiate1_gen (a := .fvar d tyA) rfl bounded) bodyRun
          obtain ⟨bsC, closed⟩ := strip_abstract annotated d 0
          simp only [Nat.zero_add, open_close tail d n tyA fresh bounded] at closed
          exact ⟨(tyA, {m with pw}) :: bsC, by
            simp only [Ix.Kernel.Expr.stripLams, closed, Option.map_some]⟩
    | _ => cases strip

/-- One raw functional reading followed by a real annotation run. -/
def ReadAnn (keyOf : Ix.Name → Key md) (levelOf : Ix.Level → Ix.Kernel.Level)
    (env : Ix.Kernel.Env md) (d : Nat) (source : Ix.Expr) (checked : Ix.Kernel.Expr md) : Prop :=
  ∃ raw, Rel (keyOf := keyOf) (levelOf := levelOf) source raw ∧ Ann env d raw checked

variable {keyOf : Ix.Name → Key md} {levelOf : Ix.Level → Ix.Kernel.Level}

theorem ReadAnn.unique {d : Nat} {source : Ix.Expr} {a b : Ix.Kernel.Expr md}
    (ha : ReadAnn keyOf levelOf env d source a) (hb : ReadAnn keyOf levelOf env d source b) : a = b := by
  obtain ⟨rawA, relA, runA⟩ := ha
  obtain ⟨rawB, relB, runB⟩ := hb
  have eq := related_unique relA relB
  subst rawB
  exact runA.unique runB

theorem read_ann_pairs {d : Nat} {xs : List Ix.Expr} {raw checked : List (Ix.Kernel.Expr md)}
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) xs raw)
    (runs : List.Forall₂ (Ann env d) raw checked) :
    List.Forall₂ (ReadAnn keyOf levelOf env d) xs checked := by
  induction read generalizing checked with
  | nil => cases runs; exact .nil
  | cons hr ht ih => cases runs with | cons ha rest => exact .cons ⟨_, hr, ha⟩ (ih rest)

/-- Reassemble successful structural application annotations at common fuel.
The source/argument witnesses still come from the actual input subcalls. -/
theorem read_ann_apps {d : Nat} {f : Ix.Expr} {fk : Ix.Kernel.Expr md}
    (hf : ReadAnn keyOf levelOf env d f fk) {args : List Ix.Expr} {ks : List (Ix.Kernel.Expr md)}
    (ha : List.Forall₂ (ReadAnn keyOf levelOf env d) args ks) :
    ReadAnn keyOf levelOf env d (args.foldl Ix.Expr.mkApp f) (fk.mkAppN ks) := by
  induction ha generalizing f fk with
  | nil => exact hf
  | cons ha _ ih =>
    obtain ⟨fr, rf, af⟩ := hf
    obtain ⟨ar, ra, aa⟩ := ha
    exact ih ⟨.app fr ar, .app _ rf ra, af.app aa⟩

theorem annotated_args_closed {d : Nat} {raw checked : List (Ix.Kernel.Expr md)}
    (runs : List.Forall₂ (Ann env d) raw checked)
    (closed : ∀ a ∈ raw, a.looseBVarsBounded 0 = true) :
    ∀ a ∈ checked, a.looseBVarsBounded 0 = true := by
  intro a ha
  obtain ⟨r, hr, F, run⟩ := Ix.Cert.ReaderUnits.forall₂_mem_right runs a ha
  exact annotateCore_looseBVars F r run (closed r hr)

theorem selectors_facts {n : Nat} {input : Array Ix.Expr} {bs out : List Ix.Expr}
    {ks : List (Ix.Kernel.Expr md)} (selected : List.Forall₂ (Selects n input) bs out)
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) bs ks) :
    ∀ k ∈ ks, Flat k ∧ k.fvarsBelow 0 ∧ k.looseBVarsBounded n = true := by
  induction selected generalizing ks with
  | nil => cases read; simp
  | cons head rest ih =>
    cases read with
    | cons hb ht =>
      obtain ⟨i, hash, bound, rfl, _⟩ := head
      cases hb
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp only [Ix.Kernel.Expr.mkBvar_eq]
        refine ⟨.bvar _, trivial, ?_⟩
        simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
      · exact ih ht k hk

theorem spine_facts {n d : Nat} {f : Ix.Kernel.Expr md} (args : List (Ix.Kernel.Expr md))
    (head : Flat f ∧ f.fvarsBelow d ∧ f.looseBVarsBounded n = true)
    (each : ∀ k ∈ args, Flat k ∧ k.fvarsBelow d ∧ k.looseBVarsBounded n = true) :
    Flat (f.mkAppN args) ∧ (f.mkAppN args).fvarsBelow d ∧
      (f.mkAppN args).looseBVarsBounded n = true := by
  induction args generalizing f with
  | nil => exact head
  | cons a args ih =>
    have arg := each a (by simp)
    apply ih
    · exact ⟨.app head.1 arg.1, ⟨head.2.1, arg.2.1⟩,
        by simp only [Ix.Kernel.Expr.looseBVarsBounded, head.2.2, arg.2.2, Bool.true_and]⟩
    · exact fun k hk => each k (List.mem_cons_of_mem _ hk)

theorem raw_prefix_strip {n : Nat} {image tail : Ix.Kernel.Expr md} (h : Lambdas n image tail) :
    ∃ bs, image.stripLams n = some (bs, tail) := by
  induction h with
  | zero => exact ⟨[], rfl⟩
  | @step n ty body tail m _ rest ih =>
    obtain ⟨bs, hs⟩ := ih
    exact ⟨(ty, m) :: bs, by simp only [Ix.Kernel.Expr.stripLams, hs, Option.map_some]⟩

/-- Positional selection of the actual annotated arguments. No distinctness
or reordering quotient is used; each selected occurrence keeps its index. -/
theorem selectors_annotated {n : Nat} {input : Array Ix.Expr} {bs out : List Ix.Expr}
    {ks args : List (Ix.Kernel.Expr md)}
    (selected : List.Forall₂ (Selects n input) bs out)
    (read : List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) bs ks)
    (inputAnn : List.Forall₂ (ReadAnn keyOf levelOf env 0) input.toList args)
    (enough : n ≤ args.length) (closed : ∀ a ∈ args, a.looseBVarsBounded 0 = true) :
    List.Forall₂ (ReadAnn keyOf levelOf env 0) out
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
/-- The actual closed recursor pass and both actual annotations determine
the checked selector substitution literally. The same produced image and
raw readings supply its terminal body; no annotation commutation, layout,
conversion or image-faithfulness identity is an input. This is not yet a
checked reduction or value theorem, and uses the exact common prefix env. -/
theorem o6_rec_annotation_layout (env : Ix.Kernel.Env md)
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
    (closed : baseK.looseBVarsBounded 0 = true)
    (baseAnn : annotateCore .verified env FB 0 baseK = .ok baseA)
    (outAnn : annotateCore .verified env FO 0 outputK = .ok outputA) :
    ∃ (imageK imageA tail : Ix.Kernel.Expr md) (argsK argsA : List (Ix.Kernel.Expr md))
      (rawBinders checkedBinders : List (Ix.Kernel.Expr md × BinderMeta)),
      baseK = imageK.mkAppN argsK ∧
      Rel (keyOf := keyOf) (levelOf := levelOf)
        (Ix.Compile.Canon.substLevels img.levelParams o.us img.value) imageK ∧
      List.Forall₂ (Rel (keyOf := keyOf) (levelOf := levelOf)) o.args.toList argsK ∧
      Ann env 0 imageK imageA ∧ List.Forall₂ (Ann env 0) argsK argsA ∧
      s.arity ≤ argsA.length ∧
      imageK.stripLams s.arity = some (rawBinders, tail) ∧
      imageA.stripLams s.arity = some (checkedBinders, tail) ∧
      baseA = imageA.mkAppN argsA ∧
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
  obtain ⟨imageA, argsA, imageRun, argRuns, checkedBase⟩ := annotate_apps argsK (baseEq ▸ baseAnn)
  have closedRaw := (closed_spine imageK argsK (baseEq ▸ closed)).2
  have closedArgs := annotated_args_closed argRuns closedRaw
  have fit : s.arity ≤ argsA.length := by
    have rawSize := CliqueRowsCoverage.forall₂_lengths argsRel
    have annSize := CliqueRowsCoverage.forall₂_lengths argRuns
    simp only [Array.length_toList] at rawSize; omega
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
  obtain ⟨FImage, imageAnn⟩ := imageRun
  obtain ⟨checkedBinders, checkedStrip⟩ := annotate_selector_tail rawStrip
    bodyFacts.1 bodyFacts.2.1 bodyFacts.2.2 imageAnn
  have inputAnn := read_ann_pairs argsRel argRuns
  have argumentsOut := selectors_annotated picked bodyArgsRel inputAnn fit closedArgs
  have more : List.Forall₂ (ReadAnn keyOf levelOf env 0)
      (o.args.extract s.arity o.args.size).toList (argsA.drop s.arity) := by
    have extraEq : (o.args.extract s.arity o.args.size).toList = o.args.toList.drop s.arity := by
      rw [Array.toList_extract, List.extract_eq_take_drop]
      have len : (o.args.toList.drop s.arity).length = o.args.size - s.arity := by simp
      rw [← len, List.take_length]
    rw [extraEq]
    exact forall₂_drop inputAnn s.arity
  have headAnn : ReadAnn keyOf levelOf env 0 (Ix.Expr.mkConst s.ixRec ls) headK :=
    ⟨headK, headOut, by cases headOut; exact ⟨1, rfl⟩⟩
  have reconstructed : ReadAnn keyOf levelOf env 0 output
      (headK.mkAppN (bodyArgsK.map (·.instantiateList (argsA.take s.arity).reverse) ++ argsA.drop s.arity)) := by
    rw [outputEq]
    simpa only [Ix.Compile.Canon.mkAppN, ← Array.foldl_toList, Array.toList_append] using
      read_ann_apps headAnn (Loop.forall₂_append argumentsOut more)
  have outputSame := reconstructed.unique ⟨outputK, outRelated, FO, outAnn⟩
  have fixedHead : headK.instantiateList (argsA.take s.arity).reverse = headK := by
    cases headOut; simp only [Ix.Kernel.Expr.instantiateList]
  refine ⟨imageK, imageA, tail, argsK, argsA, rawBinders, checkedBinders,
    baseEq, imageRel, argsRel, ⟨FImage, imageAnn⟩, argRuns, fit, rawStrip, checkedStrip, checkedBase, ?_⟩
  simpa only [bodyEq, instantiate_apps, fixedHead, ← apps_append] using outputSame.symm

end Ix.CompileCert.O6Annotation
