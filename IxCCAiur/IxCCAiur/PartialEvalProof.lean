import IxCCAiur.PartialEval
import IxCCAiur.TypedGadgets
import IxCCAiur.Backward

/-! # Certified Backward Simulation for `IxCCAiur.PartialEval`

Proves end-to-end backward simulation from `Aiur.Generic.SourceSemantics.{EvalExpr, EvalFn}`
on programs partially evaluated and pruned by `IxCC.AiurBackend.PartialEval`
(`partialEvalFns`, `partialEvalFnsPruned`, `partialEvalProg`) back to the original
`TypedLower` / `InlineFuse` program under `FieldCompatible64 F` + `Arith56WorldSpec`:

1. **World infrastructure & `pruneUnreachable` soundness** (`SameAuxWorld`,
   `WorldProvidesFn`, `WorldHasFns`, `WorldProvidesFns`, `WorldSub`,
   `evalExpr_of_worldSub`, `overlayWorld`, `pruneUnreachable_overlay_backward`).
2. **Clean/scoped expressions & strict alpha-freshness** (`isSimplePat`, `isCleanExpr`,
   `scopedExpr`, `peVarName_inj`, `NotPEGe`, `PatBindsInRange`, `BindsInRange`,
   `peExpr_syntax_props`).
3. **Heap-modulo structural value equivalence (`ValEq`) & transfer**:
   well-founded on `(bOpt, sizeOf v1)` (requiring zero acyclic-heap invariant!),
   congruent with `evalNeg`, `evalBinOp`, `projectValue`, `sliceValue`, `memberValue`,
   `loadValue`, `Builtin.apply`, `Update.value`, `matchPatternWith`, `selectArm`,
   and full `EvalExprN`/`EvalArgsN`/`EvalExitN` transfer for unchanged & library functions.
4. **Static denotation (`SValDenotes`, `EnvDenotes`), reification, pattern matching,
   and `EvalLetsN`** (`evalExprN_reifySVal_backward`, `matchPatSVal_matched_sound`,
   `matchPatSVal_noMatch_sound`, `selectArmSVal_sound`, `freshPat_matchPattern_none`,
   `freshPat_matchPattern_some`, `evalLetsN_preserves_notPEGe`, `evalExprN_wrapLetsTail_inv`).
5. **Constructive 56-bit arithmetic helper contracts (`Arith56WorldSpec`)**:
   `tryFoldHelperCall_sound`, plus constructive derivations for `check_u8`, `check_u16`,
   `check_u24`, `check_u56`, `sub_borrow_56`, `split_32_24`, `mul_56`, `divmod_56`,
   and `Fields::is_zero` (`arith56WorldSpec_of_world`).
6. **Main mutual backward simulation & top-level composition**:
   `peExpr_backward` / `peExprList_backward`, `peFn_backward`,
   `partialEvalFns_backward`, `partialEvalFnsPruned_backward`, and
   `partialEval_entry_backward` (exact identical result `rOpt = rOrig` for
   pointer-free entry arguments & results!).

Strictly zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`,
zero `bv_decide`, zero `partial`, zero `unsafe`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.PartialEvalProof

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower
  (Expr Pat Fn natLimit moduleName qualified qualifyName qualifyTy qualifyPat
   qualifyExpr qualifyPatF qualifyExprF hasDoubleColon
   isPlainExpr isPlainList isPlainArms isPlainExpr_qualifyExprF)
open IxCC.AiurBackend.Gadgets (WorldHasFn no_evalExit_of_plain evalFn_plain_inv)
open IxCC.AiurBackend.TypedLower
  (checkU8Fn checkU16Fn checkU24Fn checkU56Fn subBorrow56Fn split32_24Fn mul56Fn divmod56Fn)
open IxCC.AiurBackend.TypedGadgets (FieldCompatible64 fieldBound64)
open IxCC.AiurBackend.Backward
  (EvalExprN EvalArgsN EvalFnN EvalExitN EvalArgsExitN)
open IxCC.AiurBackend.InlineFuse (callsAny callsAnyList callsAnyArms patBoundVars pruneUnreachable)
open IxCC.AiurBackend.PartialEval

/-! ## Section 1: World Infrastructure & `pruneUnreachable` Soundness -/

section WorldInfra

variable {F : Type} [Field F] [DecidableEq F]

/-- Two worlds share identical hint typing and global constant tables. -/
structure SameAuxWorld (w1 w2 : World F) : Prop where
  typed_eq : w1.typed = w2.typed
  constant_eq : w1.constant = w2.constant
  constDepth_eq : w1.constDepth = w2.constDepth

omit [Field F] [DecidableEq F] in
theorem SameAuxWorld.refl (w : World F) : SameAuxWorld w w := ⟨rfl, rfl, rfl⟩

omit [Field F] [DecidableEq F] in
theorem SameAuxWorld.symm {w1 w2 : World F} (h : SameAuxWorld w1 w2) : SameAuxWorld w2 w1 :=
  ⟨h.typed_eq.symm, h.constant_eq.symm, h.constDepth_eq.symm⟩

omit [Field F] [DecidableEq F] in
theorem SameAuxWorld.trans {w1 w2 w3 : World F}
    (h12 : SameAuxWorld w1 w2) (h23 : SameAuxWorld w2 w3) : SameAuxWorld w1 w3 :=
  ⟨h12.typed_eq.trans h23.typed_eq, h12.constant_eq.trans h23.constant_eq,
   h12.constDepth_eq.trans h23.constDepth_eq⟩

omit [Field F] in
theorem SameAuxWorld.matchPattern_eq {w1 w2 : World F} (h : SameAuxWorld w1 w2) :
    w1.matchPattern = w2.matchPattern := by
  unfold World.matchPattern
  rw [h.constant_eq, h.constDepth_eq]

omit [Field F] in
theorem SameAuxWorld.selectArm_eq {w1 w2 : World F} (h : SameAuxWorld w1 w2)
    (types : Types) (heap : Heap F) (v : SourceValue F)
    (arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)) :
    SourceSemantics.selectArm w1 types heap v arms =
      SourceSemantics.selectArm w2 types heap v arms := by
  induction arms with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [SourceSemantics.selectArm, h.matchPattern_eq, ih]

/-- Constructive converse of `WorldHasFn`: `world` prepares non-generic function `name`
on any argument list of length `paramNames.length`. -/
def WorldProvidesFn (world : World F) (name : String) (paramNames : List String)
    (body : Aiur.Generic.Expr F) : Prop :=
  ∀ args : List (SourceValue F),
    args.length = paramNames.length →
    world.prepare name args = .ok ([], paramNames.zip args, body)

/-- Every function in `fns` is bound in `world` under `Prog::<name>` (inversion direction). -/
def WorldHasFns (world : World F) (fns : List Fn) : Prop :=
  ∀ f ∈ fns, WorldHasFn world (qualified f.name) (f.params.map Prod.fst) (qualifyExprF F f.body)

/-- Every function in `fns` can be prepared in `world` under `Prog::<name>` (constructive direction). -/
def WorldProvidesFns (world : World F) (fns : List Fn) : Prop :=
  ∀ f ∈ fns, WorldProvidesFn world (qualified f.name) (f.params.map Prod.fst) (qualifyExprF F f.body)

/-- `w1` embeds monotonically into `w2`: same auxiliary tables and every `prepare` success
in `w1` produces the exact same triple in `w2`. -/
structure WorldSub (w1 w2 : World F) : Prop where
  aux : SameAuxWorld w1 w2
  prepare_sub : ∀ nm args res, w1.prepare nm args = .ok res → w2.prepare nm args = .ok res

mutual

theorem evalExpr_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {r : SourceValue F},
      EvalExpr w1 types locals e h r h' → EvalExpr w2 types locals e h r h'
  | _, _, _, _, _, _, .block b => .block (evalExpr_of_worldSub hsub b)
  | _, _, _, _, _, _, .blockExit b => .blockExit (evalExit_of_worldSub hsub b)
  | _, _, _, _, _, _, .literal => .literal
  | _, _, _, _, _, _, .var hl => .var hl
  | _, _, _, _, _, _, .global hl hi v =>
    .global (by rw [← hsub.aux.constant_eq]; exact hl) hi (evalExpr_of_worldSub hsub v)
  | _, _, _, _, _, _, .tuple xs => .tuple (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .array xs => .array (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .repeat x => .repeat (evalExpr_of_worldSub hsub x)
  | _, _, _, _, _, _, .index x hp => .index (evalExpr_of_worldSub hsub x) hp
  | _, _, _, _, _, _, .slice x hs => .slice (evalExpr_of_worldSub hsub x) hs
  | _, _, _, _, _, _, .builtin xs ha => .builtin (evalArgs_of_worldSub hsub xs) ha
  | _, _, _, _, _, _, .update xs hu => .update (evalArgs_of_worldSub hsub xs) hu
  | _, _, _, _, _, _, .record xs => .record (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .member x hp => .member (evalExpr_of_worldSub hsub x) hp
  | _, _, _, _, _, _, .construct xs => .construct (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .constructAs xs => .constructAs (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .project x hp => .project (evalExpr_of_worldSub hsub x) hp
  | _, _, _, _, _, _, .letValue v hm b =>
    .letValue (evalExpr_of_worldSub hsub v) (by rw [← hsub.aux.matchPattern_eq]; exact hm)
      (evalExpr_of_worldSub hsub b)
  | _, _, _, _, _, _, .store v => .store (evalExpr_of_worldSub hsub v)
  | _, _, _, _, _, _, .load v hl => .load (evalExpr_of_worldSub hsub v) hl
  | _, _, _, _, _, _, .hint k ht =>
    .hint (evalExpr_of_worldSub hsub k) (by rw [← hsub.aux.typed_eq]; exact ht)
  | _, _, _, _, _, _, .neg v hop => .neg (evalExpr_of_worldSub hsub v) hop
  | _, _, _, _, _, _, .binary l r hop =>
    .binary (evalExpr_of_worldSub hsub l) (evalExpr_of_worldSub hsub r) hop
  | _, _, _, _, _, _, .call xs c => .call (evalArgs_of_worldSub hsub xs) (evalFn_of_worldSub hsub c)
  | _, _, _, _, _, _, .matchValue v hs b =>
    .matchValue (evalExpr_of_worldSub hsub v) (by rw [← hsub.aux.selectArm_eq]; exact hs)
      (evalExpr_of_worldSub hsub b)

theorem evalArgs_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs w1 types locals es h vs h' → EvalArgs w2 types locals es h vs h'
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons hd tl => .cons (evalExpr_of_worldSub hsub hd) (evalArgs_of_worldSub hsub tl)

theorem evalFn_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {name : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F},
      EvalFn w1 name args h r h' → EvalFn w2 name args h r h'
  | _, _, _, _, _, .intro hp b => .intro (hsub.prepare_sub _ _ _ hp) (evalExpr_of_worldSub hsub b)
  | _, _, _, _, _, .returned hp b => .returned (hsub.prepare_sub _ _ _ hp) (evalExit_of_worldSub hsub b)

theorem evalExit_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalExit w1 types locals e h t r h' → EvalExit w2 types locals e h t r h'
  | _, _, _, _, _, _, _, .exit v => .exit (evalExpr_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .exitPayload v => .exitPayload (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromBlock hd b => .fromBlock hd (evalExit_of_worldSub hsub b)
  | _, _, _, _, _, _, _, .fromGlobal hl hi v =>
    .fromGlobal (by rw [← hsub.aux.constant_eq]; exact hl) hi (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromTuple xs => .fromTuple (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromArray xs => .fromArray (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromRepeat v => .fromRepeat (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromIndex v => .fromIndex (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromSlice v => .fromSlice (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromBuiltin xs => .fromBuiltin (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromUpdate xs => .fromUpdate (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromRecord xs => .fromRecord (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromMember v => .fromMember (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromConstruct xs => .fromConstruct (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromConstructAs xs => .fromConstructAs (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromProject v => .fromProject (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromLetValue v => .fromLetValue (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .letBody v hm b =>
    .letBody (evalExpr_of_worldSub hsub v) (by rw [← hsub.aux.matchPattern_eq]; exact hm)
      (evalExit_of_worldSub hsub b)
  | _, _, _, _, _, _, _, .fromStore v => .fromStore (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromLoad v => .fromLoad (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromHint v => .fromHint (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .fromNeg v => .fromNeg (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .binaryLeft v => .binaryLeft (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .binaryRight l r =>
    .binaryRight (evalExpr_of_worldSub hsub l) (evalExit_of_worldSub hsub r)
  | _, _, _, _, _, _, _, .fromCall xs => .fromCall (evalArgsExit_of_worldSub hsub xs)
  | _, _, _, _, _, _, _, .fromMatchValue v => .fromMatchValue (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .matchBody v hs b =>
    .matchBody (evalExpr_of_worldSub hsub v) (by rw [← hsub.aux.selectArm_eq]; exact hs)
      (evalExit_of_worldSub hsub b)

theorem evalArgsExit_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalArgsExit w1 types locals es h t r h' → EvalArgsExit w2 types locals es h t r h'
  | _, _, _, _, _, _, _, .head v => .head (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .tail hd tl =>
    .tail (evalExpr_of_worldSub hsub hd) (evalArgsExit_of_worldSub hsub tl)

end

/-- Whether a qualified symbol belongs to `Prog::`. -/
def isProgQName (s : String) : Bool :=
  s.toList.take 6 == ['P', 'r', 'o', 'g', ':', ':']

theorem isProgQName_qualified (nm : String) : isProgQName (qualified nm) = true := by
  unfold isProgQName qualified moduleName
  change (String.toList ("Prog::" ++ nm)).take 6 == ['P', 'r', 'o', 'g', ':', ':']
  rw [String.toList_append]
  rfl

/-- Overlay `Prog` function list `fns` onto a base world `base` (leaving all non-`Prog`
entries delegated to `base`). -/
def overlayWorld (base : World F) (fns : List Fn) : World F where
  prepare := fun nm args =>
    match fns.find? (fun f => qualified f.name == nm) with
    | some f =>
      if args.length = f.params.length then
        .ok ([], (f.params.map Prod.fst).zip args, qualifyExprF F f.body)
      else
        .error (.arityMismatch nm f.params.length args.length)
    | none => base.prepare nm args
  typed := base.typed
  constant := base.constant
  constDepth := base.constDepth

omit [DecidableEq F] in
theorem sameAuxWorld_overlayWorld (base : World F) (fns : List Fn) :
    SameAuxWorld (overlayWorld base fns) base := ⟨rfl, rfl, rfl⟩

theorem qualified_inj {a b : String} (h : qualified a = qualified b) : a = b := by
  unfold qualified moduleName at h
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  have h2 := List.append_cancel_left h1
  exact String.toList_injective h2

theorem find?_eq_of_nodup {fns : List Fn} (hnd : (fns.map (·.name)).Nodup)
    {f : Fn} (hf : f ∈ fns) :
    fns.find? (fun g => qualified g.name == qualified f.name) = some f := by
  induction fns with
  | nil => cases hf
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hmem
    · simp [List.find?]
    · have hne : hd.name ≠ f.name := fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hmem)
      have hqne : (qualified hd.name == qualified f.name) = false := by
        cases hq : (qualified hd.name == qualified f.name) with
        | false => rfl
        | true => exact absurd (qualified_inj (beq_iff_eq.mp hq)) hne
      simp only [List.find?, hqne]
      exact ih hnd.2 hmem

omit [DecidableEq F] in
theorem overlayWorld_hasFns (base : World F) {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup) : WorldHasFns (overlayWorld base fns) fns := by
  intro f hf args types locals body hprep
  unfold overlayWorld at hprep
  dsimp only at hprep
  rw [find?_eq_of_nodup hnd hf] at hprep
  dsimp only at hprep
  split at hprep
  · rename_i hlen
    simp only [Except.ok.injEq, Prod.mk.injEq] at hprep
    obtain ⟨rfl, rfl, rfl⟩ := hprep
    exact ⟨rfl, by simp [hlen], rfl, rfl⟩
  · cases hprep

omit [DecidableEq F] in
theorem overlayWorld_prepare_nonProg (base : World F) (fns : List Fn)
    {nm : String} (hnp : isProgQName nm = false) (args : List (SourceValue F)) :
    (overlayWorld base fns).prepare nm args = base.prepare nm args := by
  unfold overlayWorld; dsimp only
  have hnone : fns.find? (fun f => qualified f.name == nm) = none := by
    rw [List.find?_eq_none]
    intro f _ hbeq
    have heq := beq_iff_eq.mp hbeq
    rw [← heq, isProgQName_qualified] at hnp
    cases hnp
  rw [hnone]

/-- `pruneUnreachable` is strictly backward-sound via `overlayWorld`: any `EvalFn`
derivation in `wPruned` transfers directly to `overlayWorld wPruned fns`. -/
theorem pruneUnreachable_overlay_backward {wPruned : World F} {roots : List String} {fns : List Fn}
    (hPrunedHas : WorldHasFns wPruned (pruneUnreachable roots fns))
    (hOnlyPruned : ∀ f ∈ fns, f ∉ pruneUnreachable roots fns →
      ∀ args res, wPruned.prepare (qualified f.name) args ≠ .ok res)
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn (overlayWorld wPruned fns) nm args h r h' := by
  apply evalFn_of_worldSub _ ev
  refine ⟨(sameAuxWorld_overlayWorld wPruned fns).symm, ?_⟩
  intro m a res hprep
  unfold overlayWorld; dsimp only
  cases hfind : fns.find? (fun f => qualified f.name == m) with
  | none => exact hprep
  | some f =>
    have hfmem : f ∈ fns := List.mem_of_find?_eq_some hfind
    have hbeq : (qualified f.name == m) = true :=
      List.find?_some (p := fun (g : Fn) => qualified g.name == m) hfind
    have hmeq : qualified f.name = m := beq_iff_eq.mp hbeq
    subst hmeq
    by_cases hkept : f ∈ pruneUnreachable roots fns
    · rcases res with ⟨types, locals, body⟩
      obtain ⟨rfl, hlen, rfl, rfl⟩ := hPrunedHas f hkept a types locals body hprep
      simp only [List.length_map] at hlen
      simp only [hlen, ↓reduceIte]
    · exact absurd hprep (hOnlyPruned f hfmem hkept a res)

/-- Non-`Prog` library functions (e.g. `U8Byte::check`, `UInt8::*`, `UInt32::*`, `UInt64::*`,
`Fields::*`) prepare identically on equally long argument lists regardless of pointer addresses. -/
def PrepareSameOnNonProg (wOpt wOrig : World F) : Prop :=
  ∀ m (args1 args2 : List (SourceValue F)) types loc1 body,
    isProgQName m = false →
    args1.length = args2.length →
    wOpt.prepare m args1 = .ok (types, loc1, body) →
    ∃ pnames : List String, loc1 = pnames.zip args1 ∧
      wOrig.prepare m args2 = .ok (types, pnames.zip args2, body)

/-- Every `Prog::*` function prepared in `wOpt` belongs to `optFns` (or prepares identically
in `wOrig` if outside `optFns`). -/
def PrepareClosedOnProg (wOpt wOrig : World F) (optFns : List Fn) : Prop :=
  ∀ m (args1 args2 : List (SourceValue F)) types loc1 body,
    isProgQName m = true →
    (∀ f ∈ optFns, qualified f.name ≠ m) →
    args1.length = args2.length →
    wOpt.prepare m args1 = .ok (types, loc1, body) →
    ∃ pnames : List String, loc1 = pnames.zip args1 ∧
      wOrig.prepare m args2 = .ok (types, pnames.zip args2, body)

end WorldInfra

/-! ## Section 2: Clean/Scoped Expressions & Strict Alpha-Freshness -/

section CleanAndFresh

mutual

/-- Patterns produced by `Lower`/`TypedLower`: literals, wildcards, binders, tuples,
arrays, and enum constructors (no `.orElse`, `.global`, `.load`, `.repeat`, `.record`, `.constructAs`). -/
def isSimplePat : Pat → Bool
  | .literal _ | .wildcard | .bind _ => true
  | .tuple ps | .array ps | .construct _ _ ps => isSimplePatList ps
  | _ => false

def isSimplePatList : List Pat → Bool
  | [] => true
  | p :: ps => isSimplePat p && isSimplePatList ps

end

mutual

/-- Plain expression whose `letValue`/`matchValue` patterns are all `isSimplePat`. -/
def isCleanExpr : Expr → Bool
  | .literal _ | .var _ => true
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => isCleanList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => isCleanExpr x
  | .binary _ l r => isCleanExpr l && isCleanExpr r
  | .letValue p rhs body => isSimplePat p && isCleanExpr rhs && isCleanExpr body
  | .matchValue scrut arms => isCleanExpr scrut && isCleanArms arms
  | .global _ _ | .control _ _ => false

def isCleanList : List Expr → Bool
  | [] => true
  | x :: xs => isCleanExpr x && isCleanList xs

def isCleanArms : List (Pat × Expr) → Bool
  | [] => true
  | (p, b) :: rest => isSimplePat p && isCleanExpr b && isCleanArms rest

end

mutual

theorem isCleanExpr_to_plain : ∀ e : Expr, isCleanExpr e = true → isPlainExpr e = true
  | .literal _, _ | .var _, _ => rfl
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h | .call _ _ xs, h =>
    isCleanList_to_plain xs h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h => isCleanExpr_to_plain x h
  | .binary _ l r, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [isPlainExpr, isCleanExpr_to_plain l h.1, isCleanExpr_to_plain r h.2]
  | .letValue p rhs body, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [isPlainExpr, isCleanExpr_to_plain rhs h.1.2, isCleanExpr_to_plain body h.2]
  | .matchValue scrut arms, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [isPlainExpr, isCleanExpr_to_plain scrut h.1, isCleanArms_to_plain arms h.2]
  | .global _ _, h | .control _ _, h => by cases h

theorem isCleanList_to_plain : ∀ xs : List Expr, isCleanList xs = true → isPlainList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanList, Bool.and_eq_true] at h
    simp [isPlainList, isCleanExpr_to_plain x h.1, isCleanList_to_plain xs h.2]

theorem isCleanArms_to_plain : ∀ arms : List (Pat × Expr),
    isCleanArms arms = true → isPlainArms arms = true
  | [], _ => rfl
  | (p, b) :: rest, h => by
    simp only [isCleanArms, Bool.and_eq_true] at h
    simp [isPlainArms, isCleanExpr_to_plain b h.1.2, isCleanArms_to_plain rest h.2]

end

mutual

/-- Every `.var x` occurring in `e` is bound in `bound` (or by an enclosing `let`/`match` pattern). -/
def scopedExpr (bound : List String) : Expr → Bool
  | .literal _ | .global _ _ => true
  | .var x => bound.contains x
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => scopedList bound xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => scopedExpr bound x
  | .binary _ l r => scopedExpr bound l && scopedExpr bound r
  | .letValue p rhs body => scopedExpr bound rhs && scopedExpr (patBoundVars p ++ bound) body
  | .matchValue scrut arms => scopedExpr bound scrut && scopedArms bound arms
  | .control _ _ => false

def scopedList (bound : List String) : List Expr → Bool
  | [] => true
  | x :: xs => scopedExpr bound x && scopedList bound xs

def scopedArms (bound : List String) : List (Pat × Expr) → Bool
  | [] => true
  | (p, b) :: rest => scopedExpr (patBoundVars p ++ bound) b && scopedArms bound rest

end

mutual

theorem scopedExpr_mono {b1 b2 : List String} (hsub : ∀ x, x ∈ b1 → x ∈ b2) :
    ∀ e : Expr, scopedExpr b1 e = true → scopedExpr b2 e = true
  | .literal _, _ | .global _ _, _ => rfl
  | .var x, h => List.contains_iff_mem.mpr (hsub x (List.contains_iff_mem.mp h))
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h | .call _ _ xs, h =>
    scopedList_mono hsub xs h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h => scopedExpr_mono hsub x h
  | .binary _ l r, h => by
    simp only [scopedExpr, Bool.and_eq_true] at h ⊢
    exact ⟨scopedExpr_mono hsub l h.1, scopedExpr_mono hsub r h.2⟩
  | .letValue p rhs body, h => by
    simp only [scopedExpr, Bool.and_eq_true] at h ⊢
    refine ⟨scopedExpr_mono hsub rhs h.1, scopedExpr_mono (fun x hx => ?_) body h.2⟩
    rcases List.mem_append.mp hx with h1 | h2
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (hsub x h2)
  | .matchValue scrut arms, h => by
    simp only [scopedExpr, Bool.and_eq_true] at h ⊢
    exact ⟨scopedExpr_mono hsub scrut h.1, scopedArms_mono hsub arms h.2⟩
  | .control _ _, h => by cases h

theorem scopedList_mono {b1 b2 : List String} (hsub : ∀ x, x ∈ b1 → x ∈ b2) :
    ∀ xs : List Expr, scopedList b1 xs = true → scopedList b2 xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [scopedList, Bool.and_eq_true] at h ⊢
    exact ⟨scopedExpr_mono hsub x h.1, scopedList_mono hsub xs h.2⟩

theorem scopedArms_mono {b1 b2 : List String} (hsub : ∀ x, x ∈ b1 → x ∈ b2) :
    ∀ arms : List (Pat × Expr), scopedArms b1 arms = true → scopedArms b2 arms = true
  | [], _ => rfl
  | (p, b) :: rest, h => by
    simp only [scopedArms, Bool.and_eq_true] at h ⊢
    refine ⟨scopedExpr_mono (fun x hx => ?_) b h.1, scopedArms_mono hsub rest h.2⟩
    rcases List.mem_append.mp hx with h1 | h2
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (hsub x h2)

end

theorem peVarName_inj {i j : Nat} (h : peVarName i = peVarName j) : i = j := by
  unfold peVarName at h
  have h1 := congrArg String.toList h
  simp only [String.toList_ofList, List.cons.injEq, true_and] at h1
  apply Lower.localName_inj
  unfold Lower.localName
  exact congrArg String.ofList (congrArg (List.cons 'l') h1)

theorem hasPEPrefix_peVarName (n : Nat) : hasPEPrefix (peVarName n) = true := by
  unfold hasPEPrefix peVarName
  simp only [String.toList_ofList]
  rfl

/-- Variable name `y` is distinct from every residual binder `peVarName n` with `c ≤ n`. -/
def NotPEGe (c : Nat) (y : String) : Prop :=
  ∀ n, c ≤ n → y ≠ peVarName n

theorem NotPEGe.mono {c1 c2 : Nat} {y : String} (hle : c1 ≤ c2) (h : NotPEGe c1 y) :
    NotPEGe c2 y :=
  fun n hn => h n (Nat.le_trans hle hn)

theorem notPEGe_zero_of_no_prefix {y : String} (h : hasPEPrefix y = false) : NotPEGe 0 y := by
  intro n _ heq
  subst heq
  rw [hasPEPrefix_peVarName] at h
  cases h

theorem notPEGe_peVarName_of_lt {m c : Nat} (hlt : m < c) : NotPEGe c (peVarName m) := by
  intro n hn heq
  have := peVarName_inj heq
  omega

mutual

/-- Every `.var y` inside `sv` satisfies `NotPEGe c y`. -/
def SValNotPEGe (c : Nat) : SVal → Prop
  | .lit _ | .subLit _ _ => True
  | .var y => NotPEGe c y
  | .tuple svs | .array svs | .ctor _ _ svs => SValListNotPEGe c svs
  | .ptr inner => SValNotPEGe c inner

def SValListNotPEGe (c : Nat) : List SVal → Prop
  | [] => True
  | sv :: svs => SValNotPEGe c sv ∧ SValListNotPEGe c svs

end

theorem svalListNotPEGe_iff_forall {c : Nat} {svs : List SVal} :
    SValListNotPEGe c svs ↔ ∀ sv ∈ svs, SValNotPEGe c sv := by
  induction svs with
  | nil => simp [SValListNotPEGe]
  | cons sv svs ih =>
    simp only [SValListNotPEGe, List.mem_cons, forall_eq_or_imp, ih]

mutual

theorem SValNotPEGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) :
    ∀ {sv : SVal}, SValNotPEGe c1 sv → SValNotPEGe c2 sv
  | .lit _, _ | .subLit _ _, _ => trivial
  | .var _, h => NotPEGe.mono hle h
  | .tuple _, h | .array _, h | .ctor _ _ _, h => SValListNotPEGe.mono hle h
  | .ptr inner, h => SValNotPEGe.mono hle (sv := inner) h

theorem SValListNotPEGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) :
    ∀ {svs : List SVal}, SValListNotPEGe c1 svs → SValListNotPEGe c2 svs
  | [], _ => trivial
  | _ :: _, ⟨hd, tl⟩ => ⟨hd.mono hle, tl.mono hle⟩

end

/-- Every value stored in static environment `senv` satisfies `SValNotPEGe c`. -/
def SEnvNotPEGe (c : Nat) (senv : SEnv) : Prop :=
  ∀ p ∈ senv, SValNotPEGe c p.2

theorem SEnvNotPEGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) {senv : SEnv}
    (h : SEnvNotPEGe c1 senv) : SEnvNotPEGe c2 senv :=
  fun p hp => (h p hp).mono hle

theorem SEnvNotPEGe.append {c : Nat} {s1 s2 : SEnv}
    (h1 : SEnvNotPEGe c s1) (h2 : SEnvNotPEGe c s2) : SEnvNotPEGe c (s1 ++ s2) := by
  intro p hp
  rcases List.mem_append.mp hp with hp1 | hp2
  · exact h1 p hp1
  · exact h2 p hp2

theorem SEnvNotPEGe.lookup {c : Nat} {senv : SEnv} (h : SEnvNotPEGe c senv)
    {x : String} {sv : SVal} (hl : senv.lookup x = some sv) : SValNotPEGe c sv :=
  h (x, sv) (PartialEval.mem_of_lookup_eq_some hl)

mutual

/-- Every `.bind y` occurring in pattern `p` is `peVarName n` with `lo ≤ n < hi`. -/
def PatBindsInRange (lo hi : Nat) : Pat → Prop
  | .bind y => ∃ n, lo ≤ n ∧ n < hi ∧ y = peVarName n
  | .literal _ | .wildcard => True
  | .tuple ps | .array ps | .construct _ _ ps => PatListBindsInRange lo hi ps
  | _ => False

def PatListBindsInRange (lo hi : Nat) : List Pat → Prop
  | [] => True
  | p :: ps => PatBindsInRange lo hi p ∧ PatListBindsInRange lo hi ps

end

theorem patListBindsInRange_iff_forall {lo hi : Nat} {ps : List Pat} :
    PatListBindsInRange lo hi ps ↔ ∀ p ∈ ps, PatBindsInRange lo hi p := by
  induction ps with
  | nil => simp [PatListBindsInRange]
  | cons p ps ih =>
    simp only [PatListBindsInRange, List.mem_cons, forall_eq_or_imp, ih]

mutual

theorem PatBindsInRange.mono {lo1 hi1 lo2 hi2 : Nat} (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2) :
    ∀ {p : Pat}, PatBindsInRange lo1 hi1 p → PatBindsInRange lo2 hi2 p
  | .bind _, ⟨n, hn1, hn2, hEq⟩ => ⟨n, Nat.le_trans hlo hn1, Nat.lt_of_lt_of_le hn2 hhi, hEq⟩
  | .literal _, _ | .wildcard, _ => trivial
  | .tuple _, h | .array _, h | .construct _ _ _, h => PatListBindsInRange.mono hlo hhi h
  | .global _ _, h | .orElse _ _ _, h | .load _, h | .repeat _ _, h
  | .record _ _, h | .constructAs _ _ _ _, h => False.elim h

theorem PatListBindsInRange.mono {lo1 hi1 lo2 hi2 : Nat} (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2) :
    ∀ {ps : List Pat}, PatListBindsInRange lo1 hi1 ps → PatListBindsInRange lo2 hi2 ps
  | [], _ => trivial
  | _ :: _, ⟨hd, tl⟩ => ⟨hd.mono hlo hhi, tl.mono hlo hhi⟩

end

/-- Every emitted binding `(p, rhs)` in `binds` binds only fresh `_p<n>` with `lo ≤ n < hi`. -/
def BindsInRange (lo hi : Nat) (binds : LetBinds) : Prop :=
  ∀ b ∈ binds, PatBindsInRange lo hi b.1

theorem BindsInRange.mono {lo1 hi1 lo2 hi2 : Nat} (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2)
    {binds : LetBinds} (h : BindsInRange lo1 hi1 binds) : BindsInRange lo2 hi2 binds :=
  fun b hb => (h b hb).mono hlo hhi

theorem BindsInRange.nil (lo hi : Nat) : BindsInRange lo hi [] :=
  fun _ h => by cases h

theorem BindsInRange.append {lo hi : Nat} {b1 b2 : LetBinds}
    (h1 : BindsInRange lo hi b1) (h2 : BindsInRange lo hi b2) : BindsInRange lo hi (b1 ++ b2) := by
  intro b hb
  rcases List.mem_append.mp hb with hb1 | hb2
  · exact h1 b hb1
  · exact h2 b hb2

mutual

theorem matchPatSVal_notPEGe_aux {c : Nat} :
    ∀ (p : Pat) (sv : SVal) (sbinds : SEnv),
      SValNotPEGe c sv →
      matchPatSVal p sv = .matched sbinds →
      SEnvNotPEGe c sbinds ∧ sbinds.map Prod.fst = patBoundVars p
  | .wildcard, _, sbinds, _, hm => by
    simp only [matchPatSVal, MatchDec.matched.injEq] at hm
    subst hm; exact ⟨(fun _ h => by cases h), rfl⟩
  | .bind x, sv, sbinds, hsv, hm => by
    simp only [matchPatSVal, MatchDec.matched.injEq] at hm
    subst hm
    refine ⟨fun q hq => ?_, rfl⟩
    simp only [List.mem_singleton] at hq; subst hq; exact hsv
  | .literal n, .lit m, sbinds, _, hm => by
    unfold matchPatSVal at hm
    split at hm
    · split at hm
      · simp only [MatchDec.matched.injEq] at hm; subst hm; exact ⟨(fun _ h => by cases h), rfl⟩
      · cases hm
    · cases hm
  | .literal _, .subLit _ _, _, _, hm => by
    unfold matchPatSVal at hm; split at hm <;> cases hm
  | .literal _, .var _, _, _, hm | .literal _, .tuple _, _, _, hm
  | .literal _, .array _, _, _, hm | .literal _, .ctor _ _ _, _, _, hm
  | .literal _, .ptr _, _, _, hm => by cases hm
  | .tuple ps, .tuple svs, sbinds, hsv, hm
  | .tuple ps, .array svs, sbinds, hsv, hm
  | .array ps, .tuple svs, sbinds, hsv, hm
  | .array ps, .array svs, sbinds, hsv, hm => by
    unfold matchPatSVal at hm
    split at hm
    · exact matchPatListSVal_notPEGe_aux ps svs sbinds hsv hm
    · cases hm
  | .tuple _, .lit _, _, _, hm | .tuple _, .subLit _ _, _, _, hm
  | .tuple _, .var _, _, _, hm | .tuple _, .ctor _ _ _, _, _, hm
  | .tuple _, .ptr _, _, _, hm | .array _, .lit _, _, _, hm
  | .array _, .subLit _ _, _, _, hm | .array _, .var _, _, _, hm
  | .array _, .ctor _ _ _, _, _, hm | .array _, .ptr _, _, _, hm => by cases hm
  | .construct ty c' ps, sv, sbinds, hsv, hm => by
    cases ty with
    | named tyNm targs =>
      cases targs with
      | nil =>
        cases sv with
        | ctor ty' c'' svs =>
          unfold matchPatSVal at hm
          split at hm
          · exact matchPatListSVal_notPEGe_aux ps svs sbinds hsv hm
          · cases hm
        | _ => cases hm
      | cons _ _ => cases hm
    | _ => cases hm
  | .global _ _, _, _, _, hm | .orElse _ _ _, _, _, _, hm | .load _, _, _, _, hm
  | .repeat _ _, _, _, _, hm | .record _ _, _, _, _, hm | .constructAs _ _ _ _, _, _, _, hm => by
    cases hm
termination_by p _ _ _ _ => sizeOf p

theorem matchPatListSVal_notPEGe_aux {c : Nat} :
    ∀ (ps : List Pat) (svs : List SVal) (sbinds : SEnv),
      SValListNotPEGe c svs →
      matchPatListSVal ps svs = .matched sbinds →
      SEnvNotPEGe c sbinds ∧ sbinds.map Prod.fst = InlineFuse.patListBoundVars ps
  | [], [], sbinds, _, hm => by
    simp only [matchPatListSVal, MatchDec.matched.injEq] at hm
    subst hm; exact ⟨(fun _ h => by cases h), rfl⟩
  | p :: ps, sv :: svs, sbinds, ⟨hsv, hsvs⟩, hm => by
    unfold matchPatListSVal at hm
    cases h1 : matchPatSVal p sv with
    | noMatch => rw [h1] at hm; cases hm
    | unknown => rw [h1] at hm; cases hm
    | matched b1 =>
      rw [h1] at hm
      cases h2 : matchPatListSVal ps svs with
      | noMatch => rw [h2] at hm; cases hm
      | unknown => rw [h2] at hm; cases hm
      | matched b2 =>
        rw [h2] at hm
        simp only [MatchDec.matched.injEq] at hm; subst hm
        have ⟨hb1, hn1⟩ := matchPatSVal_notPEGe_aux p sv b1 hsv h1
        have ⟨hb2, hn2⟩ := matchPatListSVal_notPEGe_aux ps svs b2 hsvs h2
        exact ⟨hb1.append hb2, by simp [InlineFuse.patListBoundVars, hn1, hn2]⟩
  | [], _ :: _, _, _, hm | _ :: _, [], _, _, hm => by cases hm
termination_by ps _ _ _ _ => sizeOf ps

end

mutual

theorem freshPat_props :
    ∀ (p : Pat) (st : PEState),
      isSimplePat p = true →
      let res := freshPat p st
      st.nextId ≤ res.2.nextId ∧
      PatBindsInRange st.nextId res.2.nextId res.1.1 ∧
      SEnvNotPEGe res.2.nextId res.1.2 ∧
      res.1.2.map Prod.fst = patBoundVars p
  | .bind x, st, _ => by
    simp only [freshPat, allocFresh, patBoundVars]
    refine ⟨by omega, ⟨st.nextId, Nat.le_refl _, Nat.lt_succ_self _, rfl⟩, ?_, rfl⟩
    intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    exact notPEGe_peVarName_of_lt (Nat.lt_succ_self _)
  | .literal _, st, _ => ⟨Nat.le_refl _, trivial, (fun _ h => by cases h), rfl⟩
  | .wildcard, st, _ => ⟨Nat.le_refl _, trivial, (fun _ h => by cases h), rfl⟩
  | .tuple ps, st, h | .array ps, st, h | .construct _ _ ps, st, h => by
    have ih := freshPatList_props ps st h
    unfold freshPat
    rcases hres : freshPatList ps st with ⟨⟨ps', bs⟩, st'⟩
    rw [hres] at ih; dsimp only at ih ⊢
    exact ih
  | .global _ _, _, h | .orElse _ _ _, _, h | .load _, _, h | .repeat _ _, _, h
  | .record _ _, _, h | .constructAs _ _ _ _, _, h => by cases h

theorem freshPatList_props :
    ∀ (ps : List Pat) (st : PEState),
      isSimplePatList ps = true →
      let res := freshPatList ps st
      st.nextId ≤ res.2.nextId ∧
      PatListBindsInRange st.nextId res.2.nextId res.1.1 ∧
      SEnvNotPEGe res.2.nextId res.1.2 ∧
      res.1.2.map Prod.fst = InlineFuse.patListBoundVars ps
  | [], st, _ => ⟨Nat.le_refl _, trivial, (fun _ h => by cases h), rfl⟩
  | p :: ps, st, h => by
    simp only [isSimplePatList, Bool.and_eq_true] at h
    have hp := freshPat_props p st h.1
    unfold freshPatList
    rcases h1 : freshPat p st with ⟨⟨p', b1⟩, st1⟩
    rw [h1] at hp; dsimp only at hp ⊢
    have hps := freshPatList_props ps st1 h.2
    rcases h2 : freshPatList ps st1 with ⟨⟨ps', b2⟩, st2⟩
    rw [h2] at hps; dsimp only at hps ⊢
    refine ⟨Nat.le_trans hp.1 hps.1,
      ⟨hp.2.1.mono (Nat.le_refl _) hps.1, hps.2.1.mono hp.1 (Nat.le_refl _)⟩,
      (hp.2.2.1.mono hps.1).append hps.2.2.1, ?_⟩
    simp [InlineFuse.patListBoundVars, hp.2.2.2, hps.2.2.2]

end

theorem tryFoldHelperCall_notPEGe {c : Nat} {nm : String} {svArgs : List SVal} {svRes : SVal}
    (hf : tryFoldHelperCall nm svArgs = some svRes) : SValNotPEGe c svRes := by
  unfold tryFoldHelperCall at hf
  split at hf <;> (try split at hf) <;>
    simp only [Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;>
    simp [SValNotPEGe, SValListNotPEGe]

private theorem emitResidual_syntax_props {lo : Nat} (bs : LetBinds) (rhs : Expr) (st : PEState)
    (hle : lo ≤ st.nextId) (hbs : BindsInRange lo st.nextId bs) :
    let res := emitResidual bs rhs st
    lo ≤ res.2.nextId ∧ BindsInRange lo res.2.nextId res.1.1 ∧
      SValNotPEGe res.2.nextId res.1.2 := by
  unfold emitResidual allocFresh; dsimp only
  refine ⟨by omega, ?_, notPEGe_peVarName_of_lt (Nat.lt_succ_self _)⟩
  refine (hbs.mono (Nat.le_refl _) (Nat.le_succ _)).append ?_
  intro b hb
  simp only [List.mem_singleton] at hb; subst hb
  exact ⟨st.nextId, hle, Nat.lt_succ_self _, rfl⟩

theorem selectArmSVal_clean_and_scoped {sv : SVal} {arms : List (Pat × Expr)}
    {sbinds : SEnv} {armBody : Expr} {c : Nat} {bound : List String}
    (hsv : SValNotPEGe c sv)
    (hclean : isCleanArms arms = true)
    (hscoped : scopedArms bound arms = true)
    (hsel : selectArmSVal sv arms = some (sbinds, armBody)) :
    isCleanExpr armBody = true ∧
    SEnvNotPEGe c sbinds ∧
    scopedExpr (sbinds.map Prod.fst ++ bound) armBody = true := by
  induction arms with
  | nil => cases hsel
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [isCleanArms, scopedArms, Bool.and_eq_true] at hclean hscoped
    unfold selectArmSVal at hsel
    cases hm : matchPatSVal p sv with
    | matched bs =>
      rw [hm] at hsel
      simp only [Option.some.injEq, Prod.mk.injEq] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      have ⟨hnb, hnames⟩ := matchPatSVal_notPEGe_aux p sv bs hsv hm
      refine ⟨hclean.1.2, hnb, ?_⟩
      rw [hnames]; exact hscoped.1
    | noMatch =>
      rw [hm] at hsel
      exact ih hclean.2 hscoped.2 hsel
    | unknown => rw [hm] at hsel; cases hsel

theorem lookup_ne_none_of_mem_map_fst {α : Type} {xs : List (String × α)} {x : String}
    (hx : x ∈ xs.map Prod.fst) : xs.lookup x ≠ none := by
  induction xs with
  | nil => simp at hx
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.mem_cons] at hx
    unfold List.lookup
    cases hkx : (x == k) with
    | true => simp
    | false =>
      rcases hx with rfl | hmem
      · simp at hkx
      · exact ih hmem

theorem map_fst_zip_eq {α β : Type} {xs : List α} {ys : List β} (hlen : xs.length = ys.length) :
    (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => cases hlen
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, ih (Nat.succ.inj hlen)]

mutual

/-- Unified syntactic invariants of `peExpr`: monotonic counter, emitted bindings strictly
in `[st.nextId, st'.nextId)`, and result `SVal` free of `_p<n>` with `n ≥ st'.nextId`. -/
theorem peExpr_syntax_props (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnClean : ∀ p ∈ fnMap, isCleanExpr p.2.body = true)
    (hfnScoped : ∀ p ∈ fnMap, scopedExpr (p.2.params.map Prod.fst) p.2.body = true) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (e : Expr) (st : PEState),
      isCleanExpr e = true →
      scopedExpr (senv.map Prod.fst) e = true →
      SEnvNotPEGe st.nextId senv →
      let res := peExpr cfg fnMap fuel curFn dynFns senv e st
      st.nextId ≤ res.2.nextId ∧
      BindsInRange st.nextId res.2.nextId res.1.1 ∧
      SValNotPEGe res.2.nextId res.1.2
  | _, _, _, _, .literal n, st, _, _, _ => by
    rw [peExpr]
    split
    · exact ⟨Nat.le_refl _, BindsInRange.nil _ _, trivial⟩
    · exact emitResidual_syntax_props [] _ st (Nat.le_refl _) (BindsInRange.nil _ _)
  | _, _, _, senv, .var x, st, _, hsc, hsenv => by
    rw [peExpr]
    cases hl : senv.lookup x with
    | some sv => exact ⟨Nat.le_refl _, BindsInRange.nil _ _, hsenv.lookup hl⟩
    | none =>
      exact absurd hl (lookup_ne_none_of_mem_map_fst (List.contains_iff_mem.mp hsc))
  | _, _, _, _, .global _ _, _, h, _, _ => by cases h
  | _, _, _, _, .control _ _, _, h, _, _ => by cases h
  | fuel, cur, dyn, senv, .tuple xs, st, h, hsc, hsenv => by
    rw [peExpr]
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st h hsc hsenv
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    exact hxs
  | fuel, cur, dyn, senv, .array xs, st, h, hsc, hsenv => by
    rw [peExpr]
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st h hsc hsenv
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    exact hxs
  | fuel, cur, dyn, senv, .construct en targs c xs, st, h, hsc, hsenv => by
    rw [peExpr]
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st h hsc hsenv
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    cases targs with
    | none => exact emitResidual_syntax_props bs _ st1 hxs.1 hxs.2.1
    | some ts =>
      cases ts with
      | nil => exact hxs
      | cons _ _ => exact emitResidual_syntax_props bs _ st1 hxs.1 hxs.2.1
  | fuel, cur, dyn, senv, .constructAs _ _ _ xs, st, h, hsc, hsenv
  | fuel, cur, dyn, senv, .record _ xs, st, h, hsc, hsenv
  | fuel, cur, dyn, senv, .update _ xs, st, h, hsc, hsenv => by
    rw [peExpr]
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st h hsc hsenv
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    exact emitResidual_syntax_props bs _ st1 hxs.1 hxs.2.1
  | fuel, cur, dyn, senv, .repeat x _, st, h, hsc, hsenv
  | fuel, cur, dyn, senv, .slice x _ _, st, h, hsc, hsenv
  | fuel, cur, dyn, senv, .member x _, st, h, hsc, hsenv
  | fuel, cur, dyn, senv, .hint _ x _, st, h, hsc, hsenv => by
    rw [peExpr]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h hsc hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
  | fuel, cur, dyn, senv, .store x, st, h, hsc, hsenv => by
    rw [peExpr]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h hsc hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    exact hx
  | fuel, cur, dyn, senv, .load x, st, h, hsc, hsenv => by
    rw [peExpr]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h hsc hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    cases sv with
    | ptr inner => exact hx
    | _ => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
  | fuel, cur, dyn, senv, .project x i, st, h, hsc, hsenv => by
    rw [peExpr]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h hsc hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    cases sv with
    | tuple svs | array svs =>
      dsimp only
      cases hi : svs[i]? with
      | some svi =>
        exact ⟨hx.1, hx.2.1, svalListNotPEGe_iff_forall.mp hx.2.2 svi (List.mem_of_getElem? hi)⟩
      | none => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
    | _ => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
  | fuel, cur, dyn, senv, .index x i, st, h, hsc, hsenv => by
    rw [peExpr]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h hsc hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    cases sv with
    | tuple svs | array svs =>
      dsimp only
      cases hi : svs[i]? with
      | some svi =>
        exact ⟨hx.1, hx.2.1, svalListNotPEGe_iff_forall.mp hx.2.2 svi (List.mem_of_getElem? hi)⟩
      | none => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
    | _ => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
  | fuel, cur, dyn, senv, .neg x, st, h, hsc, hsenv => by
    rw [peExpr]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h hsc hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    cases sv with
    | lit n =>
      cases n with
      | zero => exact ⟨hx.1, hx.2.1, trivial⟩
      | succ _ => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
    | _ => exact emitResidual_syntax_props bs _ st1 hx.1 hx.2.1
  | fuel, cur, dyn, senv, .binary op l r, st, h, hsc, hsenv => by
    simp only [isCleanExpr, scopedExpr, Bool.and_eq_true] at h hsc
    rw [peExpr]
    have hl := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv l st h.1 hsc.1 hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv l st with ⟨⟨b1, sv1⟩, st1⟩
    rw [h1] at hl; dsimp only at hl ⊢
    have hr := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv r st1 h.2 hsc.2 (hsenv.mono hl.1)
    rcases h2 : peExpr cfg fnMap fuel cur dyn senv r st1 with ⟨⟨b2, sv2⟩, st2⟩
    rw [h2] at hr; dsimp only at hr ⊢
    have hle : st.nextId ≤ st2.nextId := Nat.le_trans hl.1 hr.1
    have hboth : BindsInRange st.nextId st2.nextId (b1 ++ b2) :=
      (hl.2.1.mono (Nat.le_refl _) hr.1).append (hr.2.1.mono hl.1 (Nat.le_refl _))
    split
    · split
      · exact ⟨hle, hboth, trivial⟩
      · exact emitResidual_syntax_props _ _ st2 hle hboth
    · split
      · split
        · exact ⟨hle, hboth, trivial⟩
        · exact ⟨hle, hboth, trivial⟩
      · exact emitResidual_syntax_props _ _ st2 hle hboth
    · split
      · exact ⟨hle, hboth, trivial⟩
      · exact emitResidual_syntax_props _ _ st2 hle hboth
    · exact emitResidual_syntax_props _ _ st2 hle hboth
  | fuel, cur, dyn, senv, .builtin op xs, st, h, hsc, hsenv => by
    rw [peExpr]
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st h hsc hsenv
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    split
    · split
      · exact ⟨hxs.1, hxs.2.1, trivial⟩
      · exact emitResidual_syntax_props bs _ st1 hxs.1 hxs.2.1
    · exact emitResidual_syntax_props bs _ st1 hxs.1 hxs.2.1
  | fuel, cur, dyn, senv, .letValue p rhs body, st, h, hsc, hsenv => by
    simp only [isCleanExpr, scopedExpr, Bool.and_eq_true] at h hsc
    rw [peExpr]
    have hrhs := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv rhs st h.1.2 hsc.1 hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv rhs st with ⟨⟨bRhs, svRhs⟩, st1⟩
    rw [h1] at hrhs; dsimp only at hrhs ⊢
    cases hm : matchPatSVal p svRhs with
    | matched sbinds =>
      dsimp only
      have ⟨hnb, hnames⟩ := matchPatSVal_notPEGe_aux p svRhs sbinds hrhs.2.2 hm
      have hscBody : scopedExpr ((sbinds ++ senv).map Prod.fst) body = true := by
        rw [List.map_append, hnames]; exact hsc.2
      have hbody := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn (sbinds ++ senv) body st1
        h.2 hscBody (hnb.append (hsenv.mono hrhs.1))
      rcases h2 : peExpr cfg fnMap fuel cur dyn (sbinds ++ senv) body st1 with ⟨⟨bBody, svBody⟩, st2⟩
      rw [h2] at hbody; dsimp only at hbody ⊢
      exact ⟨Nat.le_trans hrhs.1 hbody.1,
        (hrhs.2.1.mono (Nat.le_refl _) hbody.1).append (hbody.2.1.mono hrhs.1 (Nat.le_refl _)),
        hbody.2.2⟩
    | noMatch | unknown =>
      dsimp only
      have hfp := freshPat_props p st1 h.1.1
      rcases hf : freshPat p st1 with ⟨⟨p', pBinds⟩, st2⟩
      rw [hf] at hfp; dsimp only at hfp ⊢
      have hscBody : scopedExpr ((pBinds ++ senv).map Prod.fst) body = true := by
        rw [List.map_append, hfp.2.2.2]; exact hsc.2
      have hbody := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn (pBinds ++ senv) body st2
        h.2 hscBody (hfp.2.2.1.append (hsenv.mono (Nat.le_trans hrhs.1 hfp.1)))
      rcases h2 : peExpr cfg fnMap fuel cur dyn (pBinds ++ senv) body st2 with ⟨⟨bBody, svBody⟩, st3⟩
      rw [h2] at hbody; dsimp only at hbody ⊢
      refine ⟨Nat.le_trans hrhs.1 (Nat.le_trans hfp.1 hbody.1), ?_, hbody.2.2⟩
      refine ((hrhs.2.1.mono (Nat.le_refl _) (Nat.le_trans hfp.1 hbody.1)).append ?_).append
        (hbody.2.1.mono (Nat.le_trans hrhs.1 hfp.1) (Nat.le_refl _))
      intro q hq
      simp only [List.mem_singleton] at hq; subst hq
      exact hfp.2.1.mono hrhs.1 hbody.1
  | fuel, cur, dyn, senv, .matchValue scrut arms, st, h, hsc, hsenv => by
    simp only [isCleanExpr, scopedExpr, Bool.and_eq_true] at h hsc
    rw [peExpr.eq_def]; dsimp only
    have hscS := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv scrut st h.1 hsc.1 hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv scrut st with ⟨⟨bScrut, svScrut⟩, st1⟩
    rw [h1] at hscS; dsimp only at hscS ⊢
    cases hsel : selectArmSVal svScrut arms with
    | some sb =>
      rcases sb with ⟨sbinds, armBody⟩
      dsimp only
      have _ : sizeOf armBody < sizeOf arms := selectArmSVal_sizeOf hsel
      have ⟨hcleanArm, hnb, hscArm⟩ := selectArmSVal_clean_and_scoped hscS.2.2 h.2 hsc.2 hsel
      have hscArm' : scopedExpr ((sbinds ++ senv).map Prod.fst) armBody = true := by
        rw [List.map_append]; exact hscArm
      have harm := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn (sbinds ++ senv) armBody st1
        hcleanArm hscArm' (hnb.append (hsenv.mono hscS.1))
      rcases h2 : peExpr cfg fnMap fuel cur dyn (sbinds ++ senv) armBody st1 with ⟨⟨bArm, svArm⟩, st2⟩
      rw [h2] at harm; dsimp only at harm ⊢
      exact ⟨Nat.le_trans hscS.1 harm.1,
        (hscS.2.1.mono (Nat.le_refl _) harm.1).append (harm.2.1.mono hscS.1 (Nat.le_refl _)),
        harm.2.2⟩
    | none =>
      dsimp only
      let dyn' := match cur with | some nm => if dyn.contains nm then dyn else nm :: dyn | none => dyn
      have harms := peArms_state_mono cfg fnMap hfnClean hfnScoped fuel cur dyn' senv arms st1
        h.2 hsc.2 (hsenv.mono hscS.1)
      rcases h2 : peArms cfg fnMap fuel cur dyn' senv arms st1 with ⟨arms', st2⟩
      rw [h2] at harms; dsimp only at harms ⊢
      exact emitResidual_syntax_props bScrut _ st2 (Nat.le_trans hscS.1 harms)
        (hscS.2.1.mono (Nat.le_refl _) harms)
  | fuel, cur, dyn, senv, .call nm targs xs, st, h, hsc, hsenv => by
    rw [peExpr]
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st h hsc hsenv
    rcases h1 : peExprList cfg fnMap fuel cur dyn senv xs st with ⟨⟨bArgs, svArgs⟩, st1⟩
    rw [h1] at hxs; dsimp only at hxs ⊢
    cases targs with
    | none => exact emitResidual_syntax_props bArgs _ st1 hxs.1 hxs.2.1
    | some ts =>
      cases ts with
      | cons _ _ => exact emitResidual_syntax_props bArgs _ st1 hxs.1 hxs.2.1
      | nil =>
        dsimp only
        cases hf : tryFoldHelperCall nm svArgs with
        | some svRes => exact ⟨hxs.1, hxs.2.1, tryFoldHelperCall_notPEGe hf⟩
        | none =>
          dsimp only
          cases fuel with
          | zero => exact emitResidual_syntax_props bArgs _ st1 hxs.1 hxs.2.1
          | succ fuel' =>
            dsimp only
            cases hcal : lookupEligibleCallee cfg fnMap dyn nm svArgs st1.specSteps with
            | none => exact emitResidual_syntax_props bArgs _ st1 hxs.1 hxs.2.1
            | some callee =>
              dsimp only
              have hspec := PartialEval.lookupEligibleCallee_spec hcal
              have hcp := hfnClean (nm, callee) hspec.1
              have hscCal : scopedExpr (((callee.params.map Prod.fst).zip svArgs).map Prod.fst) callee.body = true := by
                rw [map_fst_zip_eq (by simp [hspec.2.2])]
                exact hfnScoped (nm, callee) hspec.1
              have hcalSEnv : SEnvNotPEGe st1.nextId ((callee.params.map Prod.fst).zip svArgs) := by
                intro p hp
                exact svalListNotPEGe_iff_forall.mp hxs.2.2 p.2 (List.of_mem_zip hp).2
              have hbody := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel' (some nm) dyn
                ((callee.params.map Prod.fst).zip svArgs) callee.body
                { st1 with specSteps := st1.specSteps - 1 } hcp hscCal hcalSEnv
              rcases h2 : peExpr cfg fnMap fuel' (some nm) dyn
                  ((callee.params.map Prod.fst).zip svArgs) callee.body
                  { st1 with specSteps := st1.specSteps - 1 } with ⟨⟨bCal, svRes⟩, st3⟩
              rw [h2] at hbody; dsimp only at hbody ⊢
              exact ⟨Nat.le_trans hxs.1 hbody.1,
                (hxs.2.1.mono (Nat.le_refl _) hbody.1).append (hbody.2.1.mono hxs.1 (Nat.le_refl _)),
                hbody.2.2⟩
termination_by fuel _ _ _ e _ _ _ _ => (fuel, sizeOf e)

theorem peExprList_syntax_props (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnClean : ∀ p ∈ fnMap, isCleanExpr p.2.body = true)
    (hfnScoped : ∀ p ∈ fnMap, scopedExpr (p.2.params.map Prod.fst) p.2.body = true) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (xs : List Expr) (st : PEState),
      isCleanList xs = true →
      scopedList (senv.map Prod.fst) xs = true →
      SEnvNotPEGe st.nextId senv →
      let res := peExprList cfg fnMap fuel curFn dynFns senv xs st
      st.nextId ≤ res.2.nextId ∧
      BindsInRange st.nextId res.2.nextId res.1.1 ∧
      SValListNotPEGe res.2.nextId res.1.2
  | _, _, _, _, [], st, _, _, _ => by
    rw [peExprList]; exact ⟨Nat.le_refl _, BindsInRange.nil _ _, trivial⟩
  | fuel, cur, dyn, senv, x :: xs, st, h, hsc, hsenv => by
    simp only [isCleanList, scopedList, Bool.and_eq_true] at h hsc
    rw [peExprList]
    have hx := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv x st h.1 hsc.1 hsenv
    rcases h1 : peExpr cfg fnMap fuel cur dyn senv x st with ⟨⟨b1, sv1⟩, st1⟩
    rw [h1] at hx; dsimp only at hx ⊢
    have hxs := peExprList_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn senv xs st1 h.2 hsc.2 (hsenv.mono hx.1)
    rcases h2 : peExprList cfg fnMap fuel cur dyn senv xs st1 with ⟨⟨b2, svs⟩, st2⟩
    rw [h2] at hxs; dsimp only at hxs ⊢
    exact ⟨Nat.le_trans hx.1 hxs.1,
      (hx.2.1.mono (Nat.le_refl _) hxs.1).append (hxs.2.1.mono hx.1 (Nat.le_refl _)),
      ⟨hx.2.2.mono hxs.1, hxs.2.2⟩⟩
termination_by fuel _ _ _ xs _ _ _ _ => (fuel, sizeOf xs)

theorem peArms_state_mono (cfg : PEConfig) (fnMap : List (String × Fn))
    (hfnClean : ∀ p ∈ fnMap, isCleanExpr p.2.body = true)
    (hfnScoped : ∀ p ∈ fnMap, scopedExpr (p.2.params.map Prod.fst) p.2.body = true) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (arms : List (Pat × Expr)) (st : PEState),
      isCleanArms arms = true →
      scopedArms (senv.map Prod.fst) arms = true →
      SEnvNotPEGe st.nextId senv →
      st.nextId ≤ (peArms cfg fnMap fuel curFn dynFns senv arms st).2.nextId
  | _, _, _, _, [], st, _, _, _ => by rw [peArms]
  | fuel, cur, dyn, senv, (p, b) :: rest, st, h, hsc, hsenv => by
    simp only [isCleanArms, scopedArms, Bool.and_eq_true] at h hsc
    rw [peArms]
    have hfp := freshPat_props p st h.1.1
    rcases hf : freshPat p st with ⟨⟨p', pBinds⟩, st1⟩
    rw [hf] at hfp; dsimp only at hfp ⊢
    have hscB : scopedExpr ((pBinds ++ senv).map Prod.fst) b = true := by
      rw [List.map_append, hfp.2.2.2]; exact hsc.1
    have hb := peExpr_syntax_props cfg fnMap hfnClean hfnScoped fuel cur dyn (pBinds ++ senv) b st1
      h.1.2 hscB (hfp.2.2.1.append (hsenv.mono hfp.1))
    rcases h1 : peExpr cfg fnMap fuel cur dyn (pBinds ++ senv) b st1 with ⟨⟨bArm, svArm⟩, st2⟩
    rw [h1] at hb; dsimp only at hb ⊢
    have hrest := peArms_state_mono cfg fnMap hfnClean hfnScoped fuel cur dyn senv rest st2 h.2 hsc.2
      (hsenv.mono (Nat.le_trans hfp.1 hb.1))
    rcases h2 : peArms cfg fnMap fuel cur dyn senv rest st2 with ⟨rest', st3⟩
    rw [h2] at hrest; dsimp only at hrest ⊢
    exact Nat.le_trans hfp.1 (Nat.le_trans hb.1 hrest)
termination_by fuel _ _ _ arms _ _ _ _ => (fuel, sizeOf arms)

end

end CleanAndFresh

/-! ## Section 3: Heap-Modulo Structural Value Equivalence (`ValEq`) & Transfer -/

section ValEqPure

variable {F : Type}

mutual

/-- Heap-modulo structural value equivalence, bounded on `hOpt` addresses `< bOpt`.
Requires ZERO acyclic-heap invariant because recursive pointer dereference strictly
decreases `bOpt` (`a1 < bOpt`). -/
def ValEq (hOpt hOrig : Heap F) (bOpt : Nat) : SourceValue F → SourceValue F → Prop
  | .field x, .field y => x = y
  | .tuple xs, .tuple ys => ValEqList hOpt hOrig bOpt xs ys
  | .construct en1 c1 xs, .construct en2 c2 ys =>
      en1 = en2 ∧ c1 = c2 ∧ ValEqList hOpt hOrig bOpt xs ys
  | .ptr t1 a1, .ptr t2 a2 =>
      t1 = t2 ∧ ∃ (_ : a1 < bOpt) (w1 w2 : SourceValue F),
        hOpt[a1]? = some w1 ∧ hOrig[a2]? = some w2 ∧
        w1.type = t1 ∧ w2.type = t2 ∧ ValEq hOpt hOrig a1 w1 w2
  | _, _ => False
termination_by v1 _ => (bOpt, sizeOf v1)

def ValEqList (hOpt hOrig : Heap F) (bOpt : Nat) :
    List (SourceValue F) → List (SourceValue F) → Prop
  | [], [] => True
  | x :: xs, y :: ys => ValEq hOpt hOrig bOpt x y ∧ ValEqList hOpt hOrig bOpt xs ys
  | _, _ => False
termination_by xs _ => (bOpt, sizeOf xs)

end

theorem valEqList_iff_forall₂ {hOpt hOrig : Heap F} {bOpt : Nat}
    {xs ys : List (SourceValue F)} :
    ValEqList hOpt hOrig bOpt xs ys ↔ List.Forall₂ (ValEq hOpt hOrig bOpt) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [ValEqList]
    | cons _ _ => simp [ValEqList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [ValEqList]
    | cons y ys =>
      rw [ValEqList, List.forall₂_cons, ih]

theorem ValEqList.length_eq {hOpt hOrig : Heap F} {bOpt : Nat}
    {xs ys : List (SourceValue F)} (h : ValEqList hOpt hOrig bOpt xs ys) :
    xs.length = ys.length :=
  (valEqList_iff_forall₂.mp h).length_eq

theorem ValEqList.getElem?_some {hOpt hOrig : Heap F} {bOpt : Nat}
    {xs ys : List (SourceValue F)} (h : ValEqList hOpt hOrig bOpt xs ys)
    {i : Nat} {x : SourceValue F} (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ ValEq hOpt hOrig bOpt x y := by
  induction xs generalizing ys i with
  | nil => simp at hx
  | cons x0 xs ih =>
    cases ys with
    | nil => simp [ValEqList] at h
    | cons y0 ys =>
      rw [ValEqList] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx ⊢
        subst hx; exact ⟨y0, rfl, h.1⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx ⊢
        exact ih h.2 hx

theorem ValEqList.getElem?_none {hOpt hOrig : Heap F} {bOpt : Nat}
    {xs ys : List (SourceValue F)} (h : ValEqList hOpt hOrig bOpt xs ys)
    {i : Nat} (hx : xs[i]? = none) : ys[i]? = none := by
  have hlen := h.length_eq
  rw [List.getElem?_eq_none_iff] at hx ⊢
  omega

mutual

theorem ValEq.mono {hOpt hOpt' hOrig hOrig' : Heap F}
    (extOpt : Heap.Extends hOpt hOpt') (extOrig : Heap.Extends hOrig hOrig') :
    ∀ {b1 b2 : Nat} {v1 v2 : SourceValue F},
      b1 ≤ b2 → ValEq hOpt hOrig b1 v1 v2 → ValEq hOpt' hOrig' b2 v1 v2
  | b1, b2, .field x, .field y, _, h => by rw [ValEq] at h ⊢; exact h
  | b1, b2, .tuple xs, .tuple ys, hle, h => by
    rw [ValEq] at h ⊢; exact ValEqList.mono extOpt extOrig hle h
  | b1, b2, .construct en1 c1 xs, .construct en2 c2 ys, hle, h => by
    rw [ValEq] at h ⊢
    exact ⟨h.1, h.2.1, ValEqList.mono extOpt extOrig hle h.2.2⟩
  | b1, b2, .ptr t1 a1, .ptr t2 a2, hle, h => by
    rw [ValEq] at h ⊢
    rcases h with ⟨ht, hlt, w1, w2, h1, h2, hty1, hty2, hw⟩
    refine ⟨ht, Nat.lt_of_lt_of_le hlt hle, w1, w2,
      extOpt.getElem?_eq h1, extOrig.getElem?_eq h2, hty1, hty2,
      ValEq.mono extOpt extOrig (Nat.le_refl a1) hw⟩
  | _, _, .field _, .tuple _, _, h | _, _, .field _, .construct _ _ _, _, h
  | _, _, .field _, .ptr _ _, _, h | _, _, .tuple _, .field _, _, h
  | _, _, .tuple _, .construct _ _ _, _, h | _, _, .tuple _, .ptr _ _, _, h
  | _, _, .construct _ _ _, .field _, _, h | _, _, .construct _ _ _, .tuple _, _, h
  | _, _, .construct _ _ _, .ptr _ _, _, h | _, _, .ptr _ _, .field _, _, h
  | _, _, .ptr _ _, .tuple _, _, h | _, _, .ptr _ _, .construct _ _ _, _, h => by
    simp [ValEq] at h
termination_by b1 _ v1 _ _ _ => (b1, sizeOf v1)

theorem ValEqList.mono {hOpt hOpt' hOrig hOrig' : Heap F}
    (extOpt : Heap.Extends hOpt hOpt') (extOrig : Heap.Extends hOrig hOrig') :
    ∀ {b1 b2 : Nat} {xs ys : List (SourceValue F)},
      b1 ≤ b2 → ValEqList hOpt hOrig b1 xs ys → ValEqList hOpt' hOrig' b2 xs ys
  | _, _, [], [], _, _ => by rw [ValEqList]; trivial
  | _, _, x :: xs, y :: ys, hle, h => by
    rw [ValEqList] at h ⊢
    exact ⟨ValEq.mono extOpt extOrig hle h.1, ValEqList.mono extOpt extOrig hle h.2⟩
  | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h => by
    simp [ValEqList] at h
termination_by b1 _ xs _ _ _ => (b1, sizeOf xs)

end

theorem ValEq.mono_bound {hOpt hOrig : Heap F} {b1 b2 : Nat} {v1 v2 : SourceValue F}
    (hle : b1 ≤ b2) (h : ValEq hOpt hOrig b1 v1 v2) : ValEq hOpt hOrig b2 v1 v2 :=
  ValEq.mono (Heap.Extends.refl hOpt) (Heap.Extends.refl hOrig) hle h

theorem ValEq.mono_heaps {hOpt hOpt' hOrig hOrig' : Heap F} {v1 v2 : SourceValue F}
    (extOpt : Heap.Extends hOpt hOpt') (extOrig : Heap.Extends hOrig hOrig')
    (h : ValEq hOpt hOrig hOpt.length v1 v2) : ValEq hOpt' hOrig' hOpt'.length v1 v2 :=
  ValEq.mono extOpt extOrig extOpt.length_le h

theorem ValEqList.mono_heaps {hOpt hOpt' hOrig hOrig' : Heap F} {xs ys : List (SourceValue F)}
    (extOpt : Heap.Extends hOpt hOpt') (extOrig : Heap.Extends hOrig hOrig')
    (h : ValEqList hOpt hOrig hOpt.length xs ys) : ValEqList hOpt' hOrig' hOpt'.length xs ys :=
  ValEqList.mono extOpt extOrig extOpt.length_le h

mutual

theorem ValEq.type_eq {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {v1 v2 : SourceValue F}, ValEq hOpt hOrig b v1 v2 → v1.type = v2.type
  | .field _, .field _, _ => by simp [Value.type]
  | .tuple xs, .tuple ys, h => by
    rw [ValEq] at h
    simp only [Value.type, ValEqList.map_type_eq h]
  | .construct en1 _ _, .construct en2 _ _, h => by
    rw [ValEq] at h
    simp only [Value.type, h.1]
  | .ptr t1 _, .ptr t2 _, h => by
    rw [ValEq] at h
    simp only [Value.type, h.1]
  | .field _, .tuple _, h | .field _, .construct _ _ _, h | .field _, .ptr _ _, h
  | .tuple _, .field _, h | .tuple _, .construct _ _ _, h | .tuple _, .ptr _ _, h
  | .construct _ _ _, .field _, h | .construct _ _ _, .tuple _, h | .construct _ _ _, .ptr _ _, h
  | .ptr _ _, .field _, h | .ptr _ _, .tuple _, h | .ptr _ _, .construct _ _ _, h => by
    simp [ValEq] at h
termination_by v1 _ _ => sizeOf v1

theorem ValEqList.map_type_eq {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {xs ys : List (SourceValue F)}, ValEqList hOpt hOrig b xs ys →
      xs.map Value.type = ys.map Value.type
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    rw [ValEqList] at h
    simp only [List.map_cons, ValEq.type_eq h.1, ValEqList.map_type_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by
    simp [ValEqList] at h
termination_by xs _ _ => sizeOf xs

end

mutual

theorem ValEq.pointerFree_eq {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {v1 v2 : SourceValue F}, ValEq hOpt hOrig b v1 v2 → v1.pointerFree = v2.pointerFree
  | .field _, .field _, _ => by simp [Value.pointerFree]
  | .ptr _ _, .ptr _ _, _ => by simp [Value.pointerFree]
  | .tuple xs, .tuple ys, h => by
    rw [ValEq] at h
    simp only [Value.pointerFree, ValEqList.map_pointerFree_eq h]
  | .construct _ _ xs, .construct _ _ ys, h => by
    rw [ValEq] at h
    simp only [Value.pointerFree, ValEqList.map_pointerFree_eq h.2.2]
  | .field _, .tuple _, h | .field _, .construct _ _ _, h | .field _, .ptr _ _, h
  | .tuple _, .field _, h | .tuple _, .construct _ _ _, h | .tuple _, .ptr _ _, h
  | .construct _ _ _, .field _, h | .construct _ _ _, .tuple _, h | .construct _ _ _, .ptr _ _, h
  | .ptr _ _, .field _, h | .ptr _ _, .tuple _, h | .ptr _ _, .construct _ _ _, h => by
    simp [ValEq] at h
termination_by v1 _ _ => sizeOf v1

theorem ValEqList.map_pointerFree_eq {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {xs ys : List (SourceValue F)}, ValEqList hOpt hOrig b xs ys →
      xs.map Value.pointerFree = ys.map Value.pointerFree
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    rw [ValEqList] at h
    simp only [List.map_cons, ValEq.pointerFree_eq h.1, ValEqList.map_pointerFree_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by
    simp [ValEqList] at h
termination_by xs _ _ => sizeOf xs

end

mutual

theorem ValEq.eq_of_pointerFree {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {v1 v2 : SourceValue F},
      v1.pointerFree = true → ValEq hOpt hOrig b v1 v2 → v1 = v2
  | .field x, .field y, _, h => by rw [ValEq] at h; rw [h]
  | .tuple xs, .tuple ys, hpf, h => by
    rw [ValEq] at h
    simp only [Value.pointerFree, List.all_eq_true, id_eq, List.mem_map] at hpf
    have hxs : ∀ x ∈ xs, x.pointerFree = true := fun x hx => hpf x.pointerFree ⟨x, hx, rfl⟩
    rw [ValEqList.eq_of_pointerFree hxs h]
  | .construct en1 c1 xs, .construct en2 c2 ys, hpf, h => by
    rw [ValEq] at h
    simp only [Value.pointerFree, List.all_eq_true, id_eq, List.mem_map] at hpf
    have hxs : ∀ x ∈ xs, x.pointerFree = true := fun x hx => hpf x.pointerFree ⟨x, hx, rfl⟩
    rw [h.1, h.2.1, ValEqList.eq_of_pointerFree hxs h.2.2]
  | .ptr _ _, _, hpf, _ => by simp [Value.pointerFree] at hpf
  | .field _, .tuple _, _, h | .field _, .construct _ _ _, _, h | .field _, .ptr _ _, _, h
  | .tuple _, .field _, _, h | .tuple _, .construct _ _ _, _, h | .tuple _, .ptr _ _, _, h
  | .construct _ _ _, .field _, _, h | .construct _ _ _, .tuple _, _, h | .construct _ _ _, .ptr _ _, _, h => by
    simp [ValEq] at h
termination_by v1 _ _ _ => sizeOf v1

theorem ValEqList.eq_of_pointerFree {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {xs ys : List (SourceValue F)},
      (∀ x ∈ xs, x.pointerFree = true) → ValEqList hOpt hOrig b xs ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hpf, h => by
    rw [ValEqList] at h
    rw [ValEq.eq_of_pointerFree (hpf x List.mem_cons_self) h.1,
      ValEqList.eq_of_pointerFree (fun z hz => hpf z (List.mem_cons_of_mem _ hz)) h.2]
  | [], _ :: _, _, h | _ :: _, [], _, h => by
    simp [ValEqList] at h
termination_by xs _ _ _ => sizeOf xs

end

mutual

theorem ValEq.refl_of_pointerFree {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {v : SourceValue F}, v.pointerFree = true → ValEq hOpt hOrig b v v
  | .field _, _ => by rw [ValEq]
  | .tuple xs, hpf => by
    rw [ValEq]
    simp only [Value.pointerFree, List.all_eq_true, id_eq, List.mem_map] at hpf
    exact ValEqList.refl_of_pointerFree (fun x hx => hpf x.pointerFree ⟨x, hx, rfl⟩)
  | .construct _ _ xs, hpf => by
    rw [ValEq]
    simp only [Value.pointerFree, List.all_eq_true, id_eq, List.mem_map] at hpf
    exact ⟨rfl, rfl, ValEqList.refl_of_pointerFree (fun x hx => hpf x.pointerFree ⟨x, hx, rfl⟩)⟩
  | .ptr _ _, hpf => by simp [Value.pointerFree] at hpf
termination_by v _ => sizeOf v

theorem ValEqList.refl_of_pointerFree {hOpt hOrig : Heap F} {b : Nat} :
    ∀ {xs : List (SourceValue F)}, (∀ x ∈ xs, x.pointerFree = true) → ValEqList hOpt hOrig b xs xs
  | [], _ => by rw [ValEqList]; trivial
  | x :: xs, hpf => by
    rw [ValEqList]
    exact ⟨ValEq.refl_of_pointerFree (hpf x List.mem_cons_self),
      ValEqList.refl_of_pointerFree (fun z hz => hpf z (List.mem_cons_of_mem _ hz))⟩
termination_by xs _ => sizeOf xs

end

theorem value_empty_pointerFree : ∀ (v : Value F Empty), v.pointerFree = true
  | .field _ => by simp [Value.pointerFree]
  | .ptr _ a => a.elim
  | .tuple xs => by
    simp only [Value.pointerFree, List.all_eq_true, id_eq, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    have _ : sizeOf x < sizeOf (Value.tuple xs) := by
      have := List.sizeOf_lt_of_mem hx; simp [Value.tuple.sizeOf_spec]; omega
    exact value_empty_pointerFree x
  | .construct _ _ xs => by
    simp only [Value.pointerFree, List.all_eq_true, id_eq, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    have _ : sizeOf x < sizeOf (Value.construct ‹_› ‹_› xs) := by
      have := List.sizeOf_lt_of_mem hx; simp [Value.construct.sizeOf_spec]; omega
    exact value_empty_pointerFree x
termination_by v => sizeOf v

theorem Constant.toValue_pointerFree (c : Constant F) :
    (c.toValue (Address := Nat)).pointerFree = true := by
  unfold Constant.toValue
  rw [Value.pointerFree_mapAddress]
  exact value_empty_pointerFree c

/-- Pointwise `ValEq` on two runtime environments with identical variable keys and order. -/
def EnvValEq (hOpt hOrig : Heap F) (bOpt : Nat)
    (locOpt locOrig : Environment F Nat) : Prop :=
  locOpt.map Prod.fst = locOrig.map Prod.fst ∧
  ValEqList hOpt hOrig bOpt (locOpt.map Prod.snd) (locOrig.map Prod.snd)

theorem EnvValEq.nil (hOpt hOrig : Heap F) (b : Nat) : EnvValEq hOpt hOrig b [] [] :=
  ⟨rfl, by simp [ValEqList]⟩

theorem EnvValEq.mono {hOpt hOpt' hOrig hOrig' : Heap F} {b1 b2 : Nat}
    {locOpt locOrig : Environment F Nat}
    (extOpt : Heap.Extends hOpt hOpt') (extOrig : Heap.Extends hOrig hOrig') (hle : b1 ≤ b2)
    (h : EnvValEq hOpt hOrig b1 locOpt locOrig) : EnvValEq hOpt' hOrig' b2 locOpt locOrig :=
  ⟨h.1, ValEqList.mono extOpt extOrig hle h.2⟩

theorem ValEqList.append {hOpt hOrig : Heap F} {b : Nat}
    {xs1 xs2 ys1 ys2 : List (SourceValue F)}
    (h1 : ValEqList hOpt hOrig b xs1 ys1) (h2 : ValEqList hOpt hOrig b xs2 ys2) :
    ValEqList hOpt hOrig b (xs1 ++ xs2) (ys1 ++ ys2) := by
  induction xs1 generalizing ys1 with
  | nil =>
    cases ys1 with
    | nil => exact h2
    | cons _ _ => simp [ValEqList] at h1
  | cons x xs ih =>
    cases ys1 with
    | nil => simp [ValEqList] at h1
    | cons y ys =>
      rw [ValEqList] at h1
      simp only [List.cons_append]
      rw [ValEqList]
      exact ⟨h1.1, ih h1.2⟩

theorem EnvValEq.append {hOpt hOrig : Heap F} {b : Nat}
    {l1 l2 r1 r2 : Environment F Nat}
    (h1 : EnvValEq hOpt hOrig b l1 r1) (h2 : EnvValEq hOpt hOrig b l2 r2) :
    EnvValEq hOpt hOrig b (l1 ++ l2) (r1 ++ r2) :=
  ⟨by simp [h1.1, h2.1], by simp only [List.map_append]; exact h1.2.append h2.2⟩

theorem EnvValEq.zip {hOpt hOrig : Heap F} {b : Nat}
    {ks : List String} {vs1 vs2 : List (SourceValue F)}
    (hv : ValEqList hOpt hOrig b vs1 vs2) :
    EnvValEq hOpt hOrig b (ks.zip vs1) (ks.zip vs2) := by
  induction ks generalizing vs1 vs2 with
  | nil => exact EnvValEq.nil hOpt hOrig b
  | cons k ks ih =>
    cases vs1 with
    | nil =>
      cases vs2 with
      | nil => exact EnvValEq.nil hOpt hOrig b
      | cons _ _ => simp [ValEqList] at hv
    | cons v1 vs1 =>
      cases vs2 with
      | nil => simp [ValEqList] at hv
      | cons v2 vs2 =>
        rw [ValEqList] at hv
        have ⟨hk, hvs⟩ := ih hv.2
        exact ⟨by simp [hk], by simp only [List.zip_cons_cons, List.map_cons]; rw [ValEqList]; exact ⟨hv.1, hvs⟩⟩

theorem EnvValEq.find?_some {hOpt hOrig : Heap F} {b : Nat}
    {locOpt locOrig : Environment F Nat}
    (h : EnvValEq hOpt hOrig b locOpt locOrig)
    {x : String} {vOpt : SourceValue F}
    (hf : locOpt.find? (·.1 == x) = some (x, vOpt)) :
    ∃ vOrig, locOrig.find? (·.1 == x) = some (x, vOrig) ∧ ValEq hOpt hOrig b vOpt vOrig := by
  rcases h with ⟨hkeys, hvals⟩
  induction locOpt generalizing locOrig with
  | nil => simp at hf
  | cons hd1 tl1 ih =>
    cases locOrig with
    | nil => simp at hkeys
    | cons hd2 tl2 =>
      rcases hd1 with ⟨k1, v1⟩
      rcases hd2 with ⟨k2, v2⟩
      simp only [List.map_cons, List.cons.injEq] at hkeys
      rcases hkeys with ⟨rfl, hkeysTl⟩
      simp only [List.map_cons] at hvals
      rw [ValEqList] at hvals
      simp only [List.find?] at hf ⊢
      cases hkx : (k1 == x) with
      | true =>
        rw [hkx] at hf; simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact ⟨v2, rfl, hvals.1⟩
      | false =>
        rw [hkx] at hf
        exact ih hf hkeysTl hvals.2

end ValEqPure

section ValEqOps

variable {F : Type} [Field F] [DecidableEq F]

/-! ### Operation Congruence Lemmas under `ValEq` -/

omit [DecidableEq F] in
theorem evalNeg_valEq {hOpt hOrig : Heap F} {b : Nat} {v1 v2 r1 : SourceValue F}
    (hv : ValEq hOpt hOrig b v1 v2) (hop : evalNeg v1 = .ok r1) :
    evalNeg v2 = .ok r1 ∧ ValEq hOpt hOrig b r1 r1 := by
  cases v1 with
  | field x =>
    cases v2 with
    | field y =>
      rw [ValEq] at hv; subst hv
      simp only [evalNeg, Except.ok.injEq] at hop; subst hop
      exact ⟨rfl, by rw [ValEq]⟩
    | _ => simp [ValEq] at hv
  | _ => simp [evalNeg] at hop

theorem evalBinOp_valEq {hOpt hOrig : Heap F} {b : Nat} {op : BinOp}
    {x1 x2 y1 y2 r1 : SourceValue F}
    (hx : ValEq hOpt hOrig b x1 x2) (hy : ValEq hOpt hOrig b y1 y2)
    (hop : evalBinOp op x1 y1 = .ok r1) :
    evalBinOp op x2 y2 = .ok r1 ∧ ValEq hOpt hOrig b r1 r1 := by
  cases x1 with
  | field a =>
    cases x2 with
    | field a' =>
      rw [ValEq] at hx; subst hx
      cases y1 with
      | field c =>
        cases y2 with
        | field c' =>
          rw [ValEq] at hy; subst hy
          refine ⟨hop, ?_⟩
          cases op <;> simp [evalBinOp] at hop
          · subst hop; rw [ValEq]
          · subst hop; rw [ValEq]
          · subst hop; rw [ValEq]
          · split at hop
            · cases hop
            · simp only [Except.ok.injEq] at hop; subst hop; rw [ValEq]
        | _ => simp [ValEq] at hy
      | _ => simp [evalBinOp] at hop
    | _ => simp [ValEq] at hx
  | _ => simp [evalBinOp] at hop

omit [Field F] [DecidableEq F] in
theorem projectValue_valEq {hOpt hOrig : Heap F} {b : Nat} {v1 v2 r1 : SourceValue F} {i : Nat}
    (hv : ValEq hOpt hOrig b v1 v2) (hp : projectValue v1 i = .ok r1) :
    ∃ r2, projectValue v2 i = .ok r2 ∧ ValEq hOpt hOrig b r1 r2 := by
  cases v1 with
  | tuple xs =>
    cases v2 with
    | tuple ys =>
      rw [ValEq] at hv
      unfold projectValue at hp ⊢
      cases hx : xs[i]? with
      | none => simp [hx] at hp
      | some xi =>
        simp [hx] at hp; subst hp
        obtain ⟨yi, hy, heq⟩ := hv.getElem?_some hx
        exact ⟨yi, by simp [hy], heq⟩
    | _ => simp [ValEq] at hv
  | _ => simp [projectValue] at hp

private theorem forall₂_take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      List.Forall₂ R (xs.take n) (ys.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h tl => .cons h (forall₂_take n tl)

private theorem forall₂_drop {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      List.Forall₂ R (xs.drop n) (ys.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ tl => forall₂_drop n tl

private theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {a : α} {b : β}
    (h : R a b) : ∀ n, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => .cons h (forall₂_replicate h n)

omit [Field F] [DecidableEq F] in
theorem sliceValue_valEq {hOpt hOrig : Heap F} {b : Nat} {v1 v2 r1 : SourceValue F}
    {start : Nat} {stop : Option Nat}
    (hv : ValEq hOpt hOrig b v1 v2) (hs : sliceValue v1 start stop = .ok r1) :
    ∃ r2, sliceValue v2 start stop = .ok r2 ∧ ValEq hOpt hOrig b r1 r2 := by
  cases v1 with
  | tuple xs =>
    cases v2 with
    | tuple ys =>
      rw [ValEq] at hv
      have hlen := hv.length_eq
      unfold sliceValue at hs ⊢
      dsimp only at hs ⊢
      rw [← hlen]
      split at hs
      · cases hs
      · next hcond =>
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
        subst hs
        refine ⟨.tuple ((ys.drop start).take (stop.getD xs.length - start)), by simp [hcond], ?_⟩
        rw [ValEq, valEqList_iff_forall₂]
        have hf := valEqList_iff_forall₂.mp hv
        exact forall₂_take _ (forall₂_drop _ hf)
    | _ => simp [ValEq] at hv
  | _ => simp [sliceValue] at hs

omit [Field F] [DecidableEq F] in
theorem memberValue_valEq {hOpt hOrig : Heap F} {b : Nat} {types : Types} {field : FieldRef}
    {v1 v2 r1 : SourceValue F}
    (hv : ValEq hOpt hOrig b v1 v2) (hm : memberValue types field v1 = .ok r1) :
    ∃ r2, memberValue types field v2 = .ok r2 ∧ ValEq hOpt hOrig b r1 r2 := by
  cases v1 with
  | construct en1 c1 xs =>
    cases v2 with
    | construct en2 c2 ys =>
      rw [ValEq] at hv
      obtain ⟨rfl, rfl, hxs⟩ := hv
      have hlen := hxs.length_eq
      unfold memberValue at hm ⊢
      dsimp only at hm ⊢
      rw [← hlen]
      split at hm
      · cases hm
      · next hcond =>
        cases hx : xs[field.index]? with
        | none => simp [hx, bind, Except.bind, pure, Except.pure] at hm
        | some xi =>
          simp only [hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hm
          subst hm
          obtain ⟨yi, hy, heq⟩ := hxs.getElem?_some hx
          exact ⟨yi, by simp [hcond, hy], heq⟩
    | _ => simp [ValEq] at hv
  | _ => simp [memberValue] at hm

omit [Field F] [DecidableEq F] in
theorem loadValue_valEq {hOpt hOrig : Heap F} {b : Nat} {v1 v2 r1 : SourceValue F}
    (hv : ValEq hOpt hOrig b v1 v2) (hl : loadValue hOpt v1 = .ok r1) :
    ∃ r2, loadValue hOrig v2 = .ok r2 ∧ ValEq hOpt hOrig b r1 r2 := by
  cases v1 with
  | ptr t1 a1 =>
    cases v2 with
    | ptr t2 a2 =>
      rw [ValEq] at hv
      obtain ⟨rfl, hlt, w1, w2, h1, h2, hty1, hty2, hw⟩ := hv
      unfold loadValue at hl ⊢
      simp only [h1, hty1, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at hl
      subst hl
      exact ⟨w2, by simp [h2, hty2], hw.mono_bound (Nat.le_of_lt hlt)⟩
    | _ => simp [ValEq] at hv
  | _ => simp [loadValue] at hl

omit [Field F] in
theorem builtin_apply_valEq {hOpt hOrig : Heap F} {b : Nat} {op : Builtin}
    {vs1 vs2 : List (SourceValue F)} {r1 : SourceValue F}
    (hvs : ValEqList hOpt hOrig b vs1 vs2) (ha : op.apply vs1 = .ok r1) :
    ∃ r2, op.apply vs2 = .ok r2 ∧ ValEq hOpt hOrig b r1 r2 := by
  cases op with
  | ascribe _ =>
    cases vs1 with
    | nil => simp [Builtin.apply] at ha
    | cons x1 tl1 =>
      cases tl1 with
      | cons _ _ => simp [Builtin.apply] at ha
      | nil =>
        cases vs2 with
        | nil => simp [ValEqList] at hvs
        | cons x2 tl2 =>
          cases tl2 with
          | cons _ _ => rw [ValEqList] at hvs; have h2 := hvs.2; simp [ValEqList] at h2
          | nil =>
            rw [ValEqList] at hvs
            simp only [Builtin.apply, Except.ok.injEq] at ha; subst ha
            exact ⟨x2, rfl, hvs.1⟩
  | debug _ =>
    simp only [Builtin.apply, Except.ok.injEq] at ha; subst ha
    exact ⟨.tuple [], rfl, by simp [ValEq, ValEqList]⟩
  | assertEq msg =>
    cases vs1 with
    | nil => simp [Builtin.apply] at ha
    | cons x1 tl1 =>
      cases tl1 with
      | nil => simp [Builtin.apply] at ha
      | cons y1 tl1' =>
        cases tl1' with
        | cons _ _ => simp [Builtin.apply] at ha
        | nil =>
          cases vs2 with
          | nil => simp [ValEqList] at hvs
          | cons x2 tl2 =>
            cases tl2 with
            | nil => rw [ValEqList] at hvs; have h2 := hvs.2; simp [ValEqList] at h2
            | cons y2 tl2' =>
              cases tl2' with
              | cons _ _ =>
                rw [ValEqList] at hvs
                have h2 := hvs.2; rw [ValEqList] at h2
                have h3 := h2.2; simp [ValEqList] at h3
              | nil =>
                rw [ValEqList] at hvs
                have h2 := hvs.2; rw [ValEqList] at h2
                simp only [Builtin.apply] at ha ⊢
                obtain ⟨hpf, heq, rfl⟩ := evalAssertEq_ok.mp ha
                subst heq
                have hx := hvs.1.eq_of_pointerFree hpf
                have hy := h2.1.eq_of_pointerFree hpf
                subst hx; subst hy
                exact ⟨.tuple [], evalAssertEq_ok.mpr ⟨hpf, rfl, rfl⟩,
                  by simp [ValEq, ValEqList]⟩

omit [Field F] [DecidableEq F] in
theorem recordHead_order_valEq {hOpt hOrig : Heap F} {b : Nat} (head : RecordHead)
    {xs ys : List (SourceValue F)} {d1 d2 : SourceValue F}
    (hxy : ValEqList hOpt hOrig b xs ys) (hd : ValEq hOpt hOrig b d1 d2) :
    ValEqList hOpt hOrig b (head.order xs d1) (head.order ys d2) := by
  unfold RecordHead.order
  rw [ValEqList.length_eq hxy]
  rw [valEqList_iff_forall₂]
  have hmem : ∀ (slot : Option Nat),
      ValEq hOpt hOrig b ((slot.bind (xs[·]?)).getD d1) ((slot.bind (ys[·]?)).getD d2) := by
    intro slot
    cases slot with
    | none => exact hd
    | some i =>
      dsimp only [Option.bind]
      cases hx : xs[i]? with
      | none =>
        rw [ValEqList.getElem?_none hxy hx]; exact hd
      | some xi =>
        obtain ⟨yi, hy, heq⟩ := ValEqList.getElem?_some hxy hx
        rw [hy]; exact heq
  clear hd hxy
  induction head.positions ys.length with
  | nil => exact .nil
  | cons s ss ih => exact .cons (hmem s) ih

omit [Field F] [DecidableEq F] in
theorem update_replace_valEq {hOpt hOrig : Heap F} {b : Nat} (types : Types) :
    ∀ (path : UpdatePath) {base1 base2 rep1 rep2 res1 : SourceValue F},
      ValEq hOpt hOrig b base1 base2 →
      ValEq hOpt hOrig b rep1 rep2 →
      Update.replace types path base1 rep1 = some res1 →
      ∃ res2, Update.replace types path base2 rep2 = some res2 ∧ ValEq hOpt hOrig b res1 res2
  | [], _, _, rep1, rep2, res1, _, hrep, h => by
    simp only [Update.replace, Option.some.injEq] at h; subst h
    exact ⟨rep2, rfl, hrep⟩
  | step :: path, base1, base2, rep1, rep2, res1, hbase, hrep, h => by
    unfold Update.replace at h ⊢
    cases hu1 : Update.unpack types step base1 with
    | none => simp [hu1] at h
    | some vs1 =>
      simp only [hu1, bind, Option.bind_some] at h
      have hunpack : ∃ vs2, Update.unpack types step base2 = some vs2 ∧ ValEqList hOpt hOrig b vs1 vs2 := by
        unfold Update.unpack at hu1 ⊢
        cases ho : step.owner with
        | none =>
          rw [ho] at hu1
          cases base1 with
          | tuple xs =>
            cases base2 with
            | tuple ys =>
              rw [ValEq] at hbase
              dsimp only at hu1 ⊢
              split at hu1
              · simp only [Option.some.injEq] at hu1; subst hu1
                rw [← hbase.length_eq]; simp only [‹xs.length = step.width›, ↓reduceIte]
                exact ⟨ys, rfl, hbase⟩
              · cases hu1
            | _ => simp [ValEq] at hbase
          | _ => cases hu1
        | some ty =>
          rw [ho] at hu1
          cases base1 with
          | construct en1 c1 xs =>
            cases base2 with
            | construct en2 c2 ys =>
              rw [ValEq] at hbase
              obtain ⟨rfl, rfl, hxs⟩ := hbase
              dsimp only at hu1 ⊢
              split at hu1
              · next hcond =>
                simp only [Option.some.injEq] at hu1; subst hu1
                rw [← hxs.length_eq]; simp only [hcond, ↓reduceIte]
                exact ⟨ys, rfl, hxs⟩
              · cases hu1
            | _ => simp [ValEq] at hbase
          | _ => cases hu1
      obtain ⟨vs2, hu2, hvs⟩ := hunpack
      rw [hu2]; simp only [bind, Option.bind_some]
      cases hm1 : (vs1.zipIdx.mapM fun (value, index) =>
          if index == step.position then Update.replace types path value rep1 else some value) with
      | none => rw [hm1] at h; cases h
      | some ws1 =>
        simp only [hm1, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        have hmap : ∀ (k : Nat) (xs ys : List (SourceValue F)) (zs1 : List (SourceValue F)),
            ValEqList hOpt hOrig b xs ys →
            ((xs.zipIdx k).mapM fun (value, index) =>
              if index == step.position then Update.replace types path value rep1 else some value) = some zs1 →
            ∃ zs2, ((ys.zipIdx k).mapM fun (value, index) =>
              if index == step.position then Update.replace types path value rep2 else some value) = some zs2 ∧
              ValEqList hOpt hOrig b zs1 zs2 := by
          intro k xs
          induction xs generalizing k with
          | nil =>
            intro ys zs1 hxy hm
            cases ys with
            | nil =>
              simp only [List.zipIdx_nil, List.mapM_nil, pure, Option.some.injEq] at hm ⊢
              subst hm; exact ⟨[], rfl, by simp [ValEqList]⟩
            | cons _ _ => simp [ValEqList] at hxy
          | cons x xs ihxs =>
            intro ys zs1 hxy hm
            cases ys with
            | nil => simp [ValEqList] at hxy
            | cons y ys =>
              rw [ValEqList] at hxy
              simp only [List.zipIdx_cons, List.mapM_cons, bind] at hm ⊢
              cases he1 : (if k == step.position then Update.replace types path x rep1 else some x) with
              | none => rw [he1] at hm; cases hm
              | some u1 =>
                simp only [he1, Option.bind_some] at hm
                cases ht1 : ((xs.zipIdx (k + 1)).mapM fun (value, index) =>
                    if index == step.position then Update.replace types path value rep1 else some value) with
                | none => rw [ht1] at hm; cases hm
                | some us1 =>
                  simp only [ht1, Option.bind_some, pure, Option.some.injEq] at hm
                  subst hm
                  have ⟨u2, he2, hu⟩ :
                      ∃ u2, (if k == step.position then Update.replace types path y rep2 else some y) = some u2 ∧
                        ValEq hOpt hOrig b u1 u2 := by
                    by_cases hk : (k == step.position) = true
                    · simp only [hk, ↓reduceIte] at he1 ⊢
                      exact update_replace_valEq types path hxy.1 hrep he1
                    · simp only [hk, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at he1 ⊢
                      subst he1; exact ⟨y, rfl, hxy.1⟩
                  obtain ⟨us2, ht2, hus⟩ := ihxs (k + 1) ys us1 hxy.2 ht1
                  rw [he2, ht2]
                  exact ⟨u2 :: us2, rfl, by rw [ValEqList]; exact ⟨hu, hus⟩⟩
        obtain ⟨ws2, hm2, hws⟩ := hmap 0 vs1 vs2 ws1 hvs hm1
        rw [hm2]
        refine ⟨Update.pack types step ws2, rfl, ?_⟩
        unfold Update.pack
        cases step.owner with
        | none => rw [ValEq]; exact hws
        | some _ => rw [ValEq]; exact ⟨rfl, rfl, hws⟩

omit [Field F] [DecidableEq F] in
theorem update_value_valEq {hOpt hOrig : Heap F} {b : Nat} {types : Types} {paths : List UpdatePath}
    {vs1 vs2 : List (SourceValue F)} {r1 : SourceValue F}
    (hvs : ValEqList hOpt hOrig b vs1 vs2) (hu : Update.value types paths vs1 = .ok r1) :
    ∃ r2, Update.value types paths vs2 = .ok r2 ∧ ValEq hOpt hOrig b r1 r2 := by
  cases vs1 with
  | nil => simp [Update.value] at hu
  | cons b1 rs1 =>
    cases vs2 with
    | nil => simp [ValEqList] at hvs
    | cons b2 rs2 =>
      rw [ValEqList] at hvs
      unfold Update.value at hu ⊢
      cases ha1 : Update.apply types paths b1 rs1 with
      | none => simp [ha1] at hu
      | some r =>
        simp only [ha1, Except.ok.injEq] at hu; subst hu
        have happ : ∀ (ps : List UpdatePath) (x1 x2 : SourceValue F)
            (ls1 ls2 : List (SourceValue F)) (res1 : SourceValue F),
            ValEq hOpt hOrig b x1 x2 →
            ValEqList hOpt hOrig b ls1 ls2 →
            Update.apply types ps x1 ls1 = some res1 →
            ∃ res2, Update.apply types ps x2 ls2 = some res2 ∧ ValEq hOpt hOrig b res1 res2 := by
          intro ps
          induction ps with
          | nil =>
            intro x1 x2 ls1 ls2 res1 hx hls ha
            cases ls1 with
            | nil =>
              cases ls2 with
              | nil =>
                simp only [Update.apply, Option.some.injEq] at ha ⊢
                subst ha; exact ⟨x2, rfl, hx⟩
              | cons _ _ => simp [ValEqList] at hls
            | cons _ _ => simp [Update.apply] at ha
          | cons p ps ih =>
            intro x1 x2 ls1 ls2 res1 hx hls ha
            cases ls1 with
            | nil => simp [Update.apply] at ha
            | cons l1 ls1 =>
              cases ls2 with
              | nil => simp [ValEqList] at hls
              | cons l2 ls2 =>
                rw [ValEqList] at hls
                unfold Update.apply at ha ⊢
                cases hr1 : Update.replace types p x1 l1 with
                | none => simp [hr1] at ha
                | some x1' =>
                  simp only [hr1, bind, Option.bind_some] at ha
                  obtain ⟨x2', hr2, hx'⟩ := update_replace_valEq types p hx hls.1 hr1
                  rw [hr2]; simp only [bind, Option.bind_some]
                  exact ih x1' x2' ls1 ls2 res1 hx' hls.2 ha
        obtain ⟨r2, ha2, hr⟩ := happ paths b1 b2 rs1 rs2 r hvs.1 hvs.2 ha1
        exact ⟨r2, by simp [ha2], hr⟩

omit [Field F] [DecidableEq F] in
theorem reorderBindings_valEq {hOpt hOrig : Heap F} {b : Nat}
    (names : List String) (positions : List Nat)
    {b1 b2 out1 : Environment F Nat}
    (hb : EnvValEq hOpt hOrig b b1 b2)
    (hr : reorderBindings names positions b1 = some out1) :
    ∃ out2, reorderBindings names positions b2 = some out2 ∧ EnvValEq hOpt hOrig b out1 out2 := by
  induction names generalizing positions out1 with
  | nil =>
    cases positions with
    | nil =>
      simp only [reorderBindings, Option.some.injEq] at hr ⊢
      subst hr; exact ⟨[], rfl, EnvValEq.nil hOpt hOrig b⟩
    | cons _ _ => cases hr
  | cons nm nms ih =>
    cases positions with
    | nil => cases hr
    | cons idx idxs =>
      unfold reorderBindings at hr ⊢
      cases hg1 : b1[idx]? with
      | none => simp [hg1] at hr
      | some kv1 =>
        rcases kv1 with ⟨k1, v1⟩
        simp only [hg1, bind, Option.bind_some] at hr
        have hv1 : (b1.map Prod.snd)[idx]? = some v1 := by simp [hg1]
        obtain ⟨v2, hv2, hveq⟩ := hb.2.getElem?_some hv1
        have hlen : b1.length = b2.length := by
          have := congrArg List.length hb.1; simp at this; exact this
        have hidx : idx < b2.length := by
          have : idx < b1.length := (List.getElem?_eq_some_iff.mp hg1).1
          omega
        have hg2 : b2[idx]? = some (b2[idx].1, v2) := by
          have h2 : b2[idx]? = some b2[idx] := List.getElem?_eq_getElem hidx
          simp only [List.getElem?_map, h2, Option.map_some, Option.some.injEq] at hv2
          rw [h2, ← hv2]
        rw [hg2]; simp only [bind, Option.bind_some]
        cases hrest1 : reorderBindings nms idxs b1 with
        | none => simp [hrest1, Option.bind_none] at hr
        | some rest1 =>
          simp only [hrest1, Option.bind_some, pure, Option.some.injEq] at hr
          subst hr
          obtain ⟨rest2, hrest2, hreq⟩ := ih idxs hrest1
          rw [hrest2]
          refine ⟨(nm, v2) :: rest2, rfl, ?_⟩
          exact ⟨by simp [hreq.1], by simp only [List.map_cons]; rw [ValEqList]; exact ⟨hveq, hreq.2⟩⟩

omit [Field F] [DecidableEq F] in
theorem matchListWith_valEq {A : Type} {hOpt hOrig : Heap F} {b : Nat}
    {mOpt mOrig : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    (hm : ∀ a v1 v2 r1, ValEq hOpt hOrig b v1 v2 → mOpt a v1 = .ok r1 →
      match r1 with
      | none => mOrig a v2 = .ok none
      | some b1 => ∃ b2, mOrig a v2 = .ok (some b2) ∧ EnvValEq hOpt hOrig b b1 b2) :
    ∀ (ps : List A) (vs1 vs2 : List (SourceValue F)) (r1 : Option (Environment F Nat)),
      ValEqList hOpt hOrig b vs1 vs2 →
      matchListWith mOpt ps vs1 = .ok r1 →
      match r1 with
      | none => matchListWith mOrig ps vs2 = .ok none
      | some b1 => ∃ b2, matchListWith mOrig ps vs2 = .ok (some b2) ∧ EnvValEq hOpt hOrig b b1 b2
  | [], [], [], r1, _, h => by
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; exact ⟨[], rfl, EnvValEq.nil hOpt hOrig b⟩
  | p :: ps, v1 :: vs1, v2 :: vs2, r1, hvs, h => by
    rw [ValEqList] at hvs
    unfold matchListWith at h ⊢
    cases h1 : mOpt p v1 with
    | error e => simp [h1, bind, Except.bind] at h
    | ok opt1 =>
      simp only [h1, bind, Except.bind] at h
      cases opt1 with
      | none =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have h1' := hm p v1 v2 none hvs.1 h1
        rw [h1']; rfl
      | some b1 =>
        obtain ⟨b2, h1', hb⟩ := hm p v1 v2 (some b1) hvs.1 h1
        rw [h1']; simp only [bind, Except.bind]
        cases h2 : matchListWith mOpt ps vs1 with
        | error e => simp [h2] at h
        | ok opt2 =>
          simp only [h2] at h
          cases opt2 with
          | none =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have h2' := matchListWith_valEq hm ps vs1 vs2 none hvs.2 h2
            rw [h2']; rfl
          | some r1' =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            obtain ⟨r2', h2', hr⟩ := matchListWith_valEq hm ps vs1 vs2 (some r1') hvs.2 h2
            rw [h2']
            exact ⟨b2 ++ r2', rfl, hb.append hr⟩
  | [], [], _ :: _, _, hvs, _ | [], _ :: _, [], _, hvs, _
  | _ :: _, [], _ :: _, _, hvs, _ | _ :: _, _ :: _, [], _, hvs, _ => by
    simp [ValEqList] at hvs
  | [], _ :: _, _ :: _, r1, _, h | _ :: _, [], [], r1, _, h => by
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl

omit [Field F] in
theorem matchPatternWith_valEq {hOpt hOrig : Heap F} {b : Nat}
    (constant : String → Aiur.Generic.Ty → Except EvalError (Aiur.Generic.Pattern F)) :
    ∀ (depth : Nat) (types : Types) (pat : Aiur.Generic.Pattern F)
      (v1 v2 : SourceValue F) (r1 : Option (Environment F Nat)),
      ValEq hOpt hOrig b v1 v2 →
      matchPatternWith constant depth types hOpt pat v1 = .ok r1 →
      match r1 with
      | none => matchPatternWith constant depth types hOrig pat v2 = .ok none
      | some b1 =>
          ∃ b2, matchPatternWith constant depth types hOrig pat v2 = .ok (some b2) ∧
            EnvValEq hOpt hOrig b b1 b2
  | depth, types, .literal x, v1, v2, r1, hv, h => by
    cases v1 with
    | field y1 =>
      cases v2 with
      | field y2 =>
        rw [ValEq] at hv; subst hv
        cases r1 with
        | none =>
          simp only [matchPatternWith] at h ⊢; exact h
        | some b1 =>
          simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.ok.injEq] at h
          split at h
          · next heq =>
            simp only [Option.some.injEq] at h; subst h
            exact ⟨[], by simp [matchPatternWith, Aiur.Pattern.bindings, heq], EnvValEq.nil hOpt hOrig b⟩
          · cases h
      | _ => simp [ValEq] at hv
    | tuple _ =>
      cases v2 with
      | tuple _ =>
        simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [matchPatternWith, Aiur.Pattern.bindings]
      | _ => simp [ValEq] at hv
    | construct _ _ _ =>
      cases v2 with
      | construct _ _ _ =>
        simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [matchPatternWith, Aiur.Pattern.bindings]
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.ok.injEq] at h
        subst h; simp [matchPatternWith, Aiur.Pattern.bindings]
      | _ => simp [ValEq] at hv
  | _, _, .wildcard, _, _, r1, _, h => by
    simp only [matchPatternWith, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨[], by simp [matchPatternWith], EnvValEq.nil hOpt hOrig b⟩
  | _, _, .bind nm, v1, v2, r1, hv, h => by
    simp only [matchPatternWith, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[(nm, v2)], by simp [matchPatternWith],
      ⟨rfl, by simp only [List.map_cons, List.map_nil]; rw [ValEqList]; exact ⟨hv, by simp [ValEqList]⟩⟩⟩
  | depth, types, .global nm ann, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases ann with
    | none => cases h
    | some ty =>
      dsimp only at h
      cases depth with
      | zero => cases h
      | succ d =>
        dsimp only at h
        cases hc : constant nm (ty.subst types) with
        | error e => simp [hc, bind, Except.bind] at h
        | ok body =>
          simp only [hc, bind, Except.bind] at h
          have ih := matchPatternWith_valEq constant d [] body v1 v2 r1 hv h
          cases r1 with
          | none => unfold matchPatternWith; simp [hc, bind, Except.bind, ih]
          | some b1 =>
            obtain ⟨b2, hm2, hb⟩ := ih
            exact ⟨b2, by unfold matchPatternWith; simp [hc, bind, Except.bind, hm2], hb⟩
  | depth, types, .orElse left right layout, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases hl : matchPatternWith constant depth types hOpt left v1 with
    | error e => simp [hl, bind, Except.bind] at h
    | ok optL =>
      simp only [hl, bind, Except.bind] at h
      cases optL with
      | some bL1 =>
        obtain ⟨bL2, hl', hbL⟩ := matchPatternWith_valEq constant depth types left v1 v2 (some bL1) hv hl
        simp only [pure, Except.pure] at h
        cases hr1 : reorderBindings layout.names (List.range layout.names.length) bL1 with
        | none => simp [hr1] at h
        | some ord1 =>
          simp only [hr1, Except.ok.injEq] at h; subst h
          obtain ⟨ord2, hr2, hord⟩ := reorderBindings_valEq _ _ hbL hr1
          refine ⟨ord2, ?_, hord⟩
          unfold matchPatternWith; simp [hl', hr2, pure, Except.pure, bind, Except.bind]
      | none =>
        have hl' := matchPatternWith_valEq constant depth types left v1 v2 none hv hl
        cases hr : matchPatternWith constant depth types hOpt right v1 with
        | error e => simp [hr, Except.map] at h
        | ok optR =>
          simp only [hr, Except.map] at h
          cases optR with
          | none =>
            have hr' := matchPatternWith_valEq constant depth types right v1 v2 none hv hr
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            unfold matchPatternWith; simp [hl', hr', Except.map, bind, Except.bind]
          | some bR1 =>
            obtain ⟨bR2, hr', hbR⟩ := matchPatternWith_valEq constant depth types right v1 v2 (some bR1) hv hr
            cases hord1 : reorderBindings layout.names layout.rightOrder bR1 with
            | none => simp [hord1] at h
            | some ord1 =>
              simp only [hord1, pure, Except.pure, Except.ok.injEq] at h; subst h
              obtain ⟨ord2, hord2, hord⟩ := reorderBindings_valEq _ _ hbR hord1
              refine ⟨ord2, ?_, hord⟩
              unfold matchPatternWith; simp [hl', hr', hord2, Except.map, bind, Except.bind]
  | depth, types, .load pat, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases hl1 : loadValue hOpt v1 with
    | error e => simp [hl1, bind, Except.bind] at h
    | ok w1 =>
      simp only [hl1, bind, Except.bind] at h
      obtain ⟨w2, hl2, hw⟩ := loadValue_valEq hv hl1
      have ih := matchPatternWith_valEq constant depth types pat w1 w2 r1 hw h
      cases r1 with
      | none => unfold matchPatternWith; simp [hl2, bind, Except.bind, ih]
      | some b1 =>
        obtain ⟨b2, hm2, hb⟩ := ih
        exact ⟨b2, by unfold matchPatternWith; simp [hl2, bind, Except.bind, hm2], hb⟩
  | depth, types, .tuple ps, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases v1 with
    | tuple xs =>
      cases v2 with
      | tuple ys =>
        rw [ValEq] at hv
        dsimp only at h
        split at h
        · next hne =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hne' : (ps.length != ys.length) = true := by rw [← hv.length_eq]; exact hne
          unfold matchPatternWith; simp [hne']
        · next hne =>
          have hne' : ¬ (ps.length != ys.length) = true := by rw [← hv.length_eq]; exact hne
          simp only [bind, Except.bind, pure, Except.pure] at h
          have ih := matchListWith_valEq
            (fun pat a1 a2 res1 ha hm => by
              have _ : sizeOf pat.val < sizeOf (Aiur.Generic.Pattern.tuple ps) := by
                have := List.sizeOf_lt_of_mem pat.property; simp [Aiur.Generic.Pattern.tuple.sizeOf_spec]; omega
              exact matchPatternWith_valEq constant depth types pat.val a1 a2 res1 ha hm)
            ps.attach xs ys r1 hv h
          cases r1 with
          | none => unfold matchPatternWith; simp [hne', bind, Except.bind, pure, Except.pure, ih]
          | some b1 =>
            obtain ⟨b2, hm2, hb⟩ := ih
            exact ⟨b2, by unfold matchPatternWith; simp [hne', bind, Except.bind, pure, Except.pure, hm2], hb⟩
      | _ => simp [ValEq] at hv
    | field _ =>
      cases v2 with
      | field _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | construct _ _ _ =>
      cases v2 with
      | construct _ _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
  | depth, types, .array ps, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases v1 with
    | tuple xs =>
      cases v2 with
      | tuple ys =>
        rw [ValEq] at hv
        dsimp only at h
        split at h
        · next hne =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hne' : (ps.length != ys.length) = true := by rw [← hv.length_eq]; exact hne
          unfold matchPatternWith; simp [hne']
        · next hne =>
          have hne' : ¬ (ps.length != ys.length) = true := by rw [← hv.length_eq]; exact hne
          simp only [bind, Except.bind, pure, Except.pure] at h
          have ih := matchListWith_valEq
            (fun pat a1 a2 res1 ha hm => by
              have _ : sizeOf pat.val < sizeOf (Aiur.Generic.Pattern.array ps) := by
                have := List.sizeOf_lt_of_mem pat.property; simp [Aiur.Generic.Pattern.array.sizeOf_spec]; omega
              exact matchPatternWith_valEq constant depth types pat.val a1 a2 res1 ha hm)
            ps.attach xs ys r1 hv h
          cases r1 with
          | none => unfold matchPatternWith; simp [hne', bind, Except.bind, pure, Except.pure, ih]
          | some b1 =>
            obtain ⟨b2, hm2, hb⟩ := ih
            exact ⟨b2, by unfold matchPatternWith; simp [hne', bind, Except.bind, pure, Except.pure, hm2], hb⟩
      | _ => simp [ValEq] at hv
    | field _ =>
      cases v2 with
      | field _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | construct _ _ _ =>
      cases v2 with
      | construct _ _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
  | depth, types, .repeat pat n, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases v1 with
    | tuple xs =>
      cases v2 with
      | tuple ys =>
        rw [ValEq] at hv
        dsimp only at h
        split at h
        · next hne =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hne' : (ys.length != n) = true := by rw [← hv.length_eq]; exact hne
          unfold matchPatternWith; simp [hne']
        · next hne =>
          have hne' : ¬ (ys.length != n) = true := by rw [← hv.length_eq]; exact hne
          simp only [bind, Except.bind, pure, Except.pure] at h
          have ih := matchListWith_valEq
            (fun _ a1 a2 res1 ha hm => matchPatternWith_valEq constant depth types pat a1 a2 res1 ha hm)
            (List.replicate n ()) xs ys r1 hv h
          cases r1 with
          | none => unfold matchPatternWith; simp [hne', bind, Except.bind, pure, Except.pure, ih]
          | some b1 =>
            obtain ⟨b2, hm2, hb⟩ := ih
            exact ⟨b2, by unfold matchPatternWith; simp [hne', bind, Except.bind, pure, Except.pure, hm2], hb⟩
      | _ => simp [ValEq] at hv
    | field _ =>
      cases v2 with
      | field _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | construct _ _ _ =>
      cases v2 with
      | construct _ _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
  | depth, types, .record head ps, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases v1 with
    | construct en1 c1 xs =>
      cases v2 with
      | construct en2 c2 ys =>
        rw [ValEq] at hv
        obtain ⟨rfl, rfl, hxs⟩ := hv
        dsimp only at h
        split at h
        · next hcond =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          unfold matchPatternWith; simp [hcond]
        · next hcond =>
          simp only [bind, Except.bind, pure, Except.pure] at h
          split at h
          · next hlen =>
            simp only [Except.ok.injEq] at h; subst h
            have hlen' : ((head.order (ps.attach.map some) none).length != ys.length) = true := by
              rw [← hxs.length_eq]; exact hlen
            unfold matchPatternWith
            simp only [hcond, hlen', Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
          · next hlen =>
            have hlen' : ¬ ((head.order (ps.attach.map some) none).length != ys.length) = true := by
              rw [← hxs.length_eq]; exact hlen
            have ih := matchListWith_valEq
              (mOrig := fun child value => match child with
                | some pat => matchPatternWith constant depth types hOrig pat.val value
                | none => pure (some []))
              (fun child a1 a2 res1 ha hm => by
                cases child with
                | none =>
                  simp only [Except.ok.injEq] at hm
                  subst hm; exact ⟨[], rfl, EnvValEq.nil hOpt hOrig b⟩
                | some pat =>
                  exact matchPatternWith_valEq constant depth types pat.val a1 a2 res1 ha hm)
              (head.order (ps.attach.map some) none) xs ys r1 hxs h
            cases r1 with
            | none =>
              unfold matchPatternWith
              simp only [hcond, hlen', Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
              exact ih
            | some b1 =>
              obtain ⟨b2, hm2, hb⟩ := ih
              refine ⟨b2, ?_, hb⟩
              unfold matchPatternWith
              simp only [hcond, hlen', Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
              exact hm2
      | _ => simp [ValEq] at hv
    | field _ =>
      cases v2 with
      | field _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | tuple _ =>
      cases v2 with
      | tuple _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
  | depth, types, .construct ty c ps, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases v1 with
    | construct en1 c1 xs =>
      cases v2 with
      | construct en2 c2 ys =>
        rw [ValEq] at hv
        obtain ⟨rfl, rfl, hxs⟩ := hv
        dsimp only at h
        split at h
        · next hcond =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hcond' : (en1 != constructorName types ty || c1 != c || ps.length != ys.length) = true := by
            rw [← hxs.length_eq]; exact hcond
          unfold matchPatternWith; simp [hcond']
        · next hcond =>
          have hcond' : ¬ (en1 != constructorName types ty || c1 != c || ps.length != ys.length) = true := by
            rw [← hxs.length_eq]; exact hcond
          simp only [bind, Except.bind, pure, Except.pure] at h
          have ih := matchListWith_valEq
            (fun pat a1 a2 res1 ha hm => by
              have _ : sizeOf pat.val < sizeOf (Aiur.Generic.Pattern.construct ty c ps) := by
                have := List.sizeOf_lt_of_mem pat.property
                simp [Aiur.Generic.Pattern.construct.sizeOf_spec]; omega
              exact matchPatternWith_valEq constant depth types pat.val a1 a2 res1 ha hm)
            ps.attach xs ys r1 hxs h
          cases r1 with
          | none => unfold matchPatternWith; simp [hcond', bind, Except.bind, pure, Except.pure, ih]
          | some b1 =>
            obtain ⟨b2, hm2, hb⟩ := ih
            exact ⟨b2, by unfold matchPatternWith; simp [hcond', bind, Except.bind, pure, Except.pure, hm2], hb⟩
      | _ => simp [ValEq] at hv
    | field _ =>
      cases v2 with
      | field _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | tuple _ =>
      cases v2 with
      | tuple _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
  | depth, types, .constructAs _ ty c ps, v1, v2, r1, hv, h => by
    unfold matchPatternWith at h
    cases v1 with
    | construct en1 c1 xs =>
      cases v2 with
      | construct en2 c2 ys =>
        rw [ValEq] at hv
        obtain ⟨rfl, rfl, hxs⟩ := hv
        dsimp only at h
        split at h
        · next hcond =>
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          have hcond' : (en1 != constructorName types ty || c1 != c || ps.length != ys.length) = true := by
            rw [← hxs.length_eq]; exact hcond
          unfold matchPatternWith; simp [hcond']
        · next hcond =>
          have hcond' : ¬ (en1 != constructorName types ty || c1 != c || ps.length != ys.length) = true := by
            rw [← hxs.length_eq]; exact hcond
          simp only [bind, Except.bind, pure, Except.pure] at h
          have ih := matchListWith_valEq
            (fun pat a1 a2 res1 ha hm => by
              have _ : sizeOf pat.val < sizeOf (Aiur.Generic.Pattern.constructAs ‹_› ty c ps) := by
                have := List.sizeOf_lt_of_mem pat.property
                simp [Aiur.Generic.Pattern.constructAs.sizeOf_spec]; omega
              exact matchPatternWith_valEq constant depth types pat.val a1 a2 res1 ha hm)
            ps.attach xs ys r1 hxs h
          cases r1 with
          | none => unfold matchPatternWith; simp [hcond', bind, Except.bind, pure, Except.pure, ih]
          | some b1 =>
            obtain ⟨b2, hm2, hb⟩ := ih
            exact ⟨b2, by unfold matchPatternWith; simp [hcond', bind, Except.bind, pure, Except.pure, hm2], hb⟩
      | _ => simp [ValEq] at hv
    | field _ =>
      cases v2 with
      | field _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | tuple _ =>
      cases v2 with
      | tuple _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases v2 with
      | ptr _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        unfold matchPatternWith; rfl
      | _ => simp [ValEq] at hv
termination_by depth _ pat _ _ _ _ _ => (depth, sizeOf pat)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | skip
  all_goals try have := List.sizeOf_lt_of_mem pat.property
  all_goals try simp_all only [Aiur.Generic.Pattern.tuple.sizeOf_spec,
    Aiur.Generic.Pattern.array.sizeOf_spec, Aiur.Generic.Pattern.construct.sizeOf_spec,
    Aiur.Generic.Pattern.constructAs.sizeOf_spec]
  all_goals omega

omit [Field F] in
theorem matchPattern_valEq {wOpt wOrig : World F} (haux : SameAuxWorld wOpt wOrig)
    {hOpt hOrig : Heap F} {b : Nat} {types : Types} {pat : Aiur.Generic.Pattern F}
    {v1 v2 : SourceValue F} {b1 : Environment F Nat}
    (hv : ValEq hOpt hOrig b v1 v2)
    (hm : wOpt.matchPattern types hOpt pat v1 = .ok (some b1)) :
    ∃ b2, wOrig.matchPattern types hOrig pat v2 = .ok (some b2) ∧
      EnvValEq hOpt hOrig b b1 b2 := by
  unfold World.matchPattern at hm ⊢
  rw [← haux.constant_eq, ← haux.constDepth_eq]
  exact matchPatternWith_valEq wOpt.constant wOpt.constDepth types pat v1 v2 (some b1) hv hm

omit [Field F] in
theorem selectArm_valEq {wOpt wOrig : World F} (haux : SameAuxWorld wOpt wOrig)
    {hOpt hOrig : Heap F} {b : Nat} {types : Types} {v1 v2 : SourceValue F}
    {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {b1 : Environment F Nat} {body : Aiur.Generic.Expr F}
    (hv : ValEq hOpt hOrig b v1 v2)
    (hs : SourceSemantics.selectArm wOpt types hOpt v1 arms = .ok (some (b1, body))) :
    ∃ b2, SourceSemantics.selectArm wOrig types hOrig v2 arms = .ok (some (b2, body)) ∧
      EnvValEq hOpt hOrig b b1 b2 := by
  induction arms with
  | nil => simp [SourceSemantics.selectArm] at hs
  | cons hd tl ih =>
    rcases hd with ⟨p, e⟩
    unfold SourceSemantics.selectArm at hs ⊢
    cases hm : wOpt.matchPattern types hOpt p v1 with
    | error err => simp [hm, bind, Except.bind] at hs
    | ok opt =>
      simp only [hm, bind, Except.bind] at hs
      cases opt with
      | some bs =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        unfold World.matchPattern at hm ⊢
        rw [← haux.constant_eq, ← haux.constDepth_eq]
        obtain ⟨bs2, hm2, hbs⟩ := matchPatternWith_valEq wOpt.constant wOpt.constDepth types p v1 v2 (some bs) hv hm
        rw [hm2]; exact ⟨bs2, rfl, hbs⟩
      | none =>
        unfold World.matchPattern at hm ⊢
        rw [← haux.constant_eq, ← haux.constDepth_eq]
        have hm2 := matchPatternWith_valEq wOpt.constant wOpt.constDepth types p v1 v2 none hv hm
        rw [hm2]; simp only [bind, Except.bind]
        exact ih hs

/-! ### General `EvalExprN` / `EvalExitN` Transfer Under `ValEq` (for Unchanged & Library Functions) -/

mutual

theorem evalExprN_valEq_transfer {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ {types : Types} {locOpt locOrig : Environment F Nat} {e : Aiur.Generic.Expr F}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      EnvValEq hOpt1 hOrig1 hOpt1.length locOpt locOrig →
      EvalExprN wOpt d types locOpt e hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalExpr wOrig types locOrig e hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig
  | _, _, _, _, _, _, _, _, _, .literal =>
    ⟨_, _, .literal, by rw [ValEq]⟩
  | _, _, _, _, _, _, _, _, henv, .var hl =>
    let ⟨vOrig, hlOrig, hv⟩ := henv.find?_some hl
    ⟨vOrig, _, .var hlOrig, hv⟩
  | _, _, _, _, _, _, _, _, _, .global hl hi v =>
    let ⟨rOrig, hOrig2, ev', hr⟩ :=
      evalExprN_valEq_transfer haux hcall (EnvValEq.nil _ _ _) v
    ⟨rOrig, hOrig2, .global (by rw [← haux.constant_eq]; exact hl) hi ev', hr⟩
  | _, _, _, _, _, _, _, _, henv, .tuple xs =>
    let ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    ⟨.tuple vsOrig, hOrig2, .tuple ev', by rw [ValEq]; exact hvs⟩
  | _, _, _, _, _, _, _, _, henv, .array xs =>
    let ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    ⟨.tuple vsOrig, hOrig2, .array ev', by rw [ValEq]; exact hvs⟩
  | _, _, _, _, _, _, _, _, henv, .repeat x => by
    obtain ⟨vOrig, hOrig2, ev', hv⟩ := evalExprN_valEq_transfer haux hcall henv x
    refine ⟨.tuple (List.replicate _ vOrig), hOrig2, .repeat ev', ?_⟩
    rw [ValEq, valEqList_iff_forall₂]
    exact forall₂_replicate hv _
  | _, _, _, _, _, _, _, _, henv, .index x hp => by
    obtain ⟨vOrig, hOrig2, ev', hv⟩ := evalExprN_valEq_transfer haux hcall henv x
    obtain ⟨rOrig, hp', hr⟩ := projectValue_valEq hv hp
    exact ⟨rOrig, hOrig2, .index ev' hp', hr⟩
  | _, _, _, _, _, _, _, _, henv, .slice x hs => by
    obtain ⟨vOrig, hOrig2, ev', hv⟩ := evalExprN_valEq_transfer haux hcall henv x
    obtain ⟨rOrig, hs', hr⟩ := sliceValue_valEq hv hs
    exact ⟨rOrig, hOrig2, .slice ev' hs', hr⟩
  | _, _, _, _, _, _, _, _, henv, .builtin xs ha => by
    obtain ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    obtain ⟨rOrig, ha', hr⟩ := builtin_apply_valEq hvs ha
    exact ⟨rOrig, hOrig2, .builtin ev' ha', hr⟩
  | _, _, _, _, _, _, _, _, henv, .update xs hu => by
    obtain ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    obtain ⟨rOrig, hu', hr⟩ := update_value_valEq hvs hu
    exact ⟨rOrig, hOrig2, .update ev' hu', hr⟩
  | _, _, _, _, _, _, _, _, henv, .record xs => by
    obtain ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    refine ⟨_, hOrig2, .record ev', ?_⟩
    rw [ValEq]
    exact ⟨rfl, rfl, recordHead_order_valEq _ hvs (by simp [ValEq, ValEqList])⟩
  | _, _, _, _, _, _, _, _, henv, .member x hm => by
    obtain ⟨vOrig, hOrig2, ev', hv⟩ := evalExprN_valEq_transfer haux hcall henv x
    obtain ⟨rOrig, hm', hr⟩ := memberValue_valEq hv hm
    exact ⟨rOrig, hOrig2, .member ev' hm', hr⟩
  | _, _, _, _, _, _, _, _, henv, .construct xs =>
    let ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    ⟨_, hOrig2, .construct ev', by rw [ValEq]; exact ⟨rfl, rfl, hvs⟩⟩
  | _, _, _, _, _, _, _, _, henv, .constructAs xs =>
    let ⟨vsOrig, hOrig2, ev', hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    ⟨_, hOrig2, .constructAs ev', by rw [ValEq]; exact ⟨rfl, rfl, hvs⟩⟩
  | _, _, _, _, _, _, _, _, henv, .project x hp => by
    obtain ⟨vOrig, hOrig2, ev', hv⟩ := evalExprN_valEq_transfer haux hcall henv x
    obtain ⟨rOrig, hp', hr⟩ := projectValue_valEq hv hp
    exact ⟨rOrig, hOrig2, .project ev' hp', hr⟩
  | _, _, _, _, _, _, _, _, henv, .letValue v hm body => by
    obtain ⟨inOrig, hOrigM, evV, hin⟩ := evalExprN_valEq_transfer haux hcall henv v
    obtain ⟨bOrig, hmOrig, hb⟩ := matchPattern_valEq haux hin hm
    have henvM := henv.mono v.heap_extends evV.heap_extends v.heap_extends.length_le
    obtain ⟨rOrig, hOrig2, evB, hr⟩ := evalExprN_valEq_transfer haux hcall (hb.append henvM) body
    exact ⟨rOrig, hOrig2, .letValue evV hmOrig evB, hr⟩
  | _, _, _, _, _, _, _, _, henv, .store v => by
    obtain ⟨inOrig, hOrigM, evV, hin⟩ := evalExprN_valEq_transfer haux hcall henv v
    refine ⟨.ptr inOrig.type hOrigM.length, hOrigM ++ [inOrig], .store evV, ?_⟩
    rw [ValEq]
    refine ⟨hin.type_eq, by simp, _, inOrig, by simp, by simp, rfl, rfl, ?_⟩
    exact ValEq.mono (Heap.Extends.append_right _ _) (Heap.Extends.append_right _ _) (Nat.le_refl _) hin
  | _, _, _, _, _, _, _, _, henv, .load v hl => by
    obtain ⟨pOrig, hOrig2, evV, hp⟩ := evalExprN_valEq_transfer haux hcall henv v
    obtain ⟨rOrig, hlOrig, hr⟩ := loadValue_valEq hp hl
    exact ⟨rOrig, hOrig2, .load evV hlOrig, hr⟩
  | _, _, _, _, _, _, _, _, henv, .hint k ht => by
    obtain ⟨_, hOrig2, evK, _⟩ := evalExprN_valEq_transfer haux hcall henv k
    exact ⟨_, hOrig2, .hint evK (by rw [← haux.typed_eq]; exact ht),
      ValEq.refl_of_pointerFree (Constant.toValue_pointerFree _)⟩
  | _, _, _, _, _, _, _, _, henv, .neg v hop => by
    obtain ⟨inOrig, hOrig2, evV, hin⟩ := evalExprN_valEq_transfer haux hcall henv v
    obtain ⟨hop', hr⟩ := evalNeg_valEq hin hop
    exact ⟨_, hOrig2, .neg evV hop', hr⟩
  | _, _, _, _, _, _, _, _, henv, .binary l r hop => by
    obtain ⟨xOrig, hOrigM, evL, hx⟩ := evalExprN_valEq_transfer haux hcall henv l
    have henvM := henv.mono l.heap_extends evL.heap_extends l.heap_extends.length_le
    obtain ⟨yOrig, hOrig2, evR, hy⟩ := evalExprN_valEq_transfer haux hcall henvM r
    have hx2 := hx.mono_heaps r.heap_extends evR.heap_extends
    obtain ⟨hop', hr⟩ := evalBinOp_valEq hx2 hy hop
    exact ⟨_, hOrig2, .binary evL evR hop', hr⟩
  | _, _, _, _, _, _, _, _, henv, .call hlt xs cal => by
    obtain ⟨vsOrig, hOrigM, evArgs, hvs⟩ := evalArgsN_valEq_transfer haux hcall henv xs
    obtain ⟨rOrig, hOrig2, evCal, hr⟩ := hcall hlt hvs cal
    exact ⟨rOrig, hOrig2, .call evArgs evCal, hr⟩
  | _, _, _, _, _, _, _, _, henv, .matchValue v hs br => by
    obtain ⟨inOrig, hOrigM, evV, hin⟩ := evalExprN_valEq_transfer haux hcall henv v
    obtain ⟨bOrig, hsOrig, hb⟩ := selectArm_valEq haux hin hs
    have henvM := henv.mono v.heap_extends evV.heap_extends v.heap_extends.length_le
    obtain ⟨rOrig, hOrig2, evB, hr⟩ := evalExprN_valEq_transfer haux hcall (hb.append henvM) br
    exact ⟨rOrig, hOrig2, .matchValue evV hsOrig evB, hr⟩
  | _, _, _, _, _, _, _, _, henv, .block b =>
    let ⟨rOrig, hOrig2, evB, hr⟩ := evalExprN_valEq_transfer haux hcall henv b
    ⟨rOrig, hOrig2, .block evB, hr⟩
  | _, _, _, _, _, _, _, _, henv, .blockExit b =>
    let ⟨rOrig, hOrig2, evB, hr⟩ := evalExitN_valEq_transfer haux hcall henv b
    ⟨rOrig, hOrig2, .blockExit evB, hr⟩

theorem evalArgsN_valEq_transfer {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ {types : Types} {locOpt locOrig : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {vsOpt : List (SourceValue F)},
      EnvValEq hOpt1 hOrig1 hOpt1.length locOpt locOrig →
      EvalArgsN wOpt d types locOpt es hOpt1 vsOpt hOpt2 →
      ∃ vsOrig hOrig2,
        EvalArgs wOrig types locOrig es hOrig1 vsOrig hOrig2 ∧
        ValEqList hOpt2 hOrig2 hOpt2.length vsOpt vsOrig
  | _, _, _, _, _, _, _, _, _, .nil =>
    ⟨[], _, .nil, by simp [ValEqList]⟩
  | _, _, _, _, _, _, _, _, henv, .cons hd tl => by
    obtain ⟨vOrig, hOrigM, evHd, hv⟩ := evalExprN_valEq_transfer haux hcall henv hd
    have henvM := henv.mono hd.heap_extends evHd.heap_extends hd.heap_extends.length_le
    obtain ⟨vsOrig, hOrig2, evTl, hvs⟩ := evalArgsN_valEq_transfer haux hcall henvM tl
    have hv2 := hv.mono_heaps tl.heap_extends evTl.heap_extends
    exact ⟨vOrig :: vsOrig, hOrig2, .cons evHd evTl, by rw [ValEqList]; exact ⟨hv2, hvs⟩⟩

theorem evalExitN_valEq_transfer {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ {types : Types} {locOpt locOrig : Environment F Nat} {e : Aiur.Generic.Expr F}
      {hOpt1 hOpt2 hOrig1 : Heap F} {t : ExitTarget} {rOpt : SourceValue F},
      EnvValEq hOpt1 hOrig1 hOpt1.length locOpt locOrig →
      EvalExitN wOpt d types locOpt e hOpt1 t rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalExit wOrig types locOrig e hOrig1 t rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig
  | _, _, _, _, _, _, _, _, _, henv, .exit v =>
    let ⟨r, h, ev, hr⟩ := evalExprN_valEq_transfer haux hcall henv v; ⟨r, h, .exit ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .exitPayload v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .exitPayload ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromBlock hd b =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv b; ⟨r, h, .fromBlock hd ev, hr⟩
  | _, _, _, _, _, _, _, _, _, _, .fromGlobal hl hi v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall (EnvValEq.nil _ _ _) v
    ⟨r, h, .fromGlobal (by rw [← haux.constant_eq]; exact hl) hi ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromTuple xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromTuple ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromArray xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromArray ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromRepeat v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromRepeat ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromIndex v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromIndex ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromSlice v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromSlice ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromBuiltin xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromBuiltin ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromUpdate xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromUpdate ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromRecord xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromRecord ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromMember v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromMember ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromConstruct xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromConstruct ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromConstructAs xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromConstructAs ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromProject v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromProject ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromLetValue v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromLetValue ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .letBody v hm b => by
    obtain ⟨inOrig, hOrigM, evV, hin⟩ := evalExprN_valEq_transfer haux hcall henv v
    obtain ⟨bOrig, hmOrig, hb⟩ := matchPattern_valEq haux hin hm
    have henvM := henv.mono v.heap_extends evV.heap_extends v.heap_extends.length_le
    obtain ⟨rOrig, hOrig2, evB, hr⟩ := evalExitN_valEq_transfer haux hcall (hb.append henvM) b
    exact ⟨rOrig, hOrig2, .letBody evV hmOrig evB, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromStore v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromStore ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromLoad v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromLoad ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromHint v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromHint ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromNeg v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromNeg ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .binaryLeft v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .binaryLeft ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .binaryRight l r => by
    obtain ⟨_, hOrigM, evL, _⟩ := evalExprN_valEq_transfer haux hcall henv l
    have henvM := henv.mono l.heap_extends evL.heap_extends l.heap_extends.length_le
    obtain ⟨rOrig, hOrig2, evR, hr⟩ := evalExitN_valEq_transfer haux hcall henvM r
    exact ⟨rOrig, hOrig2, .binaryRight evL evR, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromCall xs =>
    let ⟨r, h, ev, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henv xs; ⟨r, h, .fromCall ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .fromMatchValue v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .fromMatchValue ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .matchBody v hs b => by
    obtain ⟨inOrig, hOrigM, evV, hin⟩ := evalExprN_valEq_transfer haux hcall henv v
    obtain ⟨bOrig, hsOrig, hb⟩ := selectArm_valEq haux hin hs
    have henvM := henv.mono v.heap_extends evV.heap_extends v.heap_extends.length_le
    obtain ⟨rOrig, hOrig2, evB, hr⟩ := evalExitN_valEq_transfer haux hcall (hb.append henvM) b
    exact ⟨rOrig, hOrig2, .matchBody evV hsOrig evB, hr⟩

theorem evalArgsExitN_valEq_transfer {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ {types : Types} {locOpt locOrig : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {t : ExitTarget} {rOpt : SourceValue F},
      EnvValEq hOpt1 hOrig1 hOpt1.length locOpt locOrig →
      EvalArgsExitN wOpt d types locOpt es hOpt1 t rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalArgsExit wOrig types locOrig es hOrig1 t rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig
  | _, _, _, _, _, _, _, _, _, henv, .head v =>
    let ⟨r, h, ev, hr⟩ := evalExitN_valEq_transfer haux hcall henv v; ⟨r, h, .head ev, hr⟩
  | _, _, _, _, _, _, _, _, _, henv, .tail hd tl => by
    obtain ⟨_, hOrigM, evHd, _⟩ := evalExprN_valEq_transfer haux hcall henv hd
    have henvM := henv.mono hd.heap_extends evHd.heap_extends hd.heap_extends.length_le
    obtain ⟨rOrig, hOrig2, evTl, hr⟩ := evalArgsExitN_valEq_transfer haux hcall henvM tl
    exact ⟨rOrig, hOrig2, .tail evHd evTl, hr⟩

end

end ValEqOps

/-! ## Section 4: `SValDenotes`, `EnvDenotes`, `reifySVal`, `matchPatSVal`, `freshPat`, `EvalLetsN` -/

section SValPure

variable {F : Type} [Field F]

mutual

/-- Denotation relating a compile-time `SVal` (in residual scope `locOpt`, heap `hOpt`)
to an original runtime value `vOrig` (in heap `hOrig`). Deferred `.ptr inner` values
dereference directly in `hOrig` with zero allocation required in `hOpt`! -/
def SValDenotes (hOpt hOrig : Heap F) (locOpt : Environment F Nat) :
    SVal → SourceValue F → Prop
  | .lit n, v => n < natLimit ∧ v = .field (n : F)
  | .subLit a b, v => a < b ∧ b < natLimit ∧ v = .field ((a : F) - (b : F))
  | .var y, v => ∃ vOpt, locOpt.find? (·.1 == y) = some (y, vOpt) ∧
      ValEq hOpt hOrig hOpt.length vOpt v
  | .tuple svs, v => ∃ vs, v = .tuple vs ∧ SValListDenotes hOpt hOrig locOpt svs vs
  | .array svs, v => ∃ vs, v = .tuple vs ∧ SValListDenotes hOpt hOrig locOpt svs vs
  | .ctor en c svs, v => ∃ vs, v = .construct (qualifyName en) c vs ∧
      SValListDenotes hOpt hOrig locOpt svs vs
  | .ptr inner, v => ∃ t a wOrig, v = .ptr t a ∧ hOrig[a]? = some wOrig ∧
      wOrig.type = t ∧ SValDenotes hOpt hOrig locOpt inner wOrig

def SValListDenotes (hOpt hOrig : Heap F) (locOpt : Environment F Nat) :
    List SVal → List (SourceValue F) → Prop
  | [], [] => True
  | sv :: svs, v :: vs => SValDenotes hOpt hOrig locOpt sv v ∧
      SValListDenotes hOpt hOrig locOpt svs vs
  | _, _ => False

end

theorem svalListDenotes_length_eq {hOpt hOrig : Heap F} {locOpt : Environment F Nat}
    {svs : List SVal} {vs : List (SourceValue F)}
    (h : SValListDenotes hOpt hOrig locOpt svs vs) : svs.length = vs.length := by
  induction svs generalizing vs with
  | nil => cases vs with | nil => rfl | cons _ _ => exact False.elim h
  | cons _ _ ih =>
    cases vs with
    | nil => exact False.elim h
    | cons _ _ => exact congrArg Nat.succ (ih h.2)

theorem svalListDenotes_getElem?_some {hOpt hOrig : Heap F} {locOpt : Environment F Nat}
    {svs : List SVal} {vs : List (SourceValue F)}
    (h : SValListDenotes hOpt hOrig locOpt svs vs) {i : Nat} {svi : SVal}
    (hi : svs[i]? = some svi) :
    ∃ vi, vs[i]? = some vi ∧ SValDenotes hOpt hOrig locOpt svi vi := by
  induction svs generalizing vs i with
  | nil => simp at hi
  | cons sv svs ih =>
    cases vs with
    | nil => exact False.elim h
    | cons v vs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢
        subst hi; exact ⟨v, rfl, h.1⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi ⊢
        exact ih h.2 hi

mutual

theorem SValDenotes.lift {hOpt1 hOpt2 hOrig1 hOrig2 : Heap F}
    {locOpt1 locOpt2 : Environment F Nat} {c : Nat}
    (extOpt : Heap.Extends hOpt1 hOpt2) (extOrig : Heap.Extends hOrig1 hOrig2)
    (hloc : ∀ y, NotPEGe c y → locOpt2.find? (·.1 == y) = locOpt1.find? (·.1 == y)) :
    ∀ {sv : SVal} {v : SourceValue F},
      SValNotPEGe c sv →
      SValDenotes hOpt1 hOrig1 locOpt1 sv v →
      SValDenotes hOpt2 hOrig2 locOpt2 sv v
  | .lit _, _, _, h => h
  | .subLit _ _, _, _, h => h
  | .var y, _, hnot, ⟨vOpt, hf, hv⟩ =>
    ⟨vOpt, (hloc y hnot).trans hf, hv.mono_heaps extOpt extOrig⟩
  | .tuple _, _, hnot, ⟨vs, hv, hvs⟩ =>
    ⟨vs, hv, SValListDenotes.lift extOpt extOrig hloc hnot hvs⟩
  | .array _, _, hnot, ⟨vs, hv, hvs⟩ =>
    ⟨vs, hv, SValListDenotes.lift extOpt extOrig hloc hnot hvs⟩
  | .ctor _ _ _, _, hnot, ⟨vs, hv, hvs⟩ =>
    ⟨vs, hv, SValListDenotes.lift extOpt extOrig hloc hnot hvs⟩
  | .ptr inner, _, hnot, ⟨t, a, wOrig, hv, ha, hty, hw⟩ =>
    ⟨t, a, wOrig, hv, extOrig.getElem?_eq ha, hty,
      SValDenotes.lift extOpt extOrig hloc (sv := inner) hnot hw⟩

theorem SValListDenotes.lift {hOpt1 hOpt2 hOrig1 hOrig2 : Heap F}
    {locOpt1 locOpt2 : Environment F Nat} {c : Nat}
    (extOpt : Heap.Extends hOpt1 hOpt2) (extOrig : Heap.Extends hOrig1 hOrig2)
    (hloc : ∀ y, NotPEGe c y → locOpt2.find? (·.1 == y) = locOpt1.find? (·.1 == y)) :
    ∀ {svs : List SVal} {vs : List (SourceValue F)},
      SValListNotPEGe c svs →
      SValListDenotes hOpt1 hOrig1 locOpt1 svs vs →
      SValListDenotes hOpt2 hOrig2 locOpt2 svs vs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨hn1, hns⟩, ⟨h1, hs⟩ =>
    ⟨SValDenotes.lift extOpt extOrig hloc hn1 h1, SValListDenotes.lift extOpt extOrig hloc hns hs⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => False.elim h

end

mutual

theorem SValDenotes.mono_heaps {hOpt1 hOpt2 hOrig1 hOrig2 : Heap F} {locOpt : Environment F Nat}
    (extOpt : Heap.Extends hOpt1 hOpt2) (extOrig : Heap.Extends hOrig1 hOrig2) :
    ∀ {sv : SVal} {v : SourceValue F},
      SValDenotes hOpt1 hOrig1 locOpt sv v → SValDenotes hOpt2 hOrig2 locOpt sv v
  | .lit _, _, h => h
  | .subLit _ _, _, h => h
  | .var _, _, ⟨vOpt, hf, hv⟩ => ⟨vOpt, hf, hv.mono_heaps extOpt extOrig⟩
  | .tuple _, _, ⟨vs, rfl, hvs⟩ => ⟨vs, rfl, SValListDenotes.mono_heaps extOpt extOrig hvs⟩
  | .array _, _, ⟨vs, rfl, hvs⟩ => ⟨vs, rfl, SValListDenotes.mono_heaps extOpt extOrig hvs⟩
  | .ctor _ _ _, _, ⟨vs, rfl, hvs⟩ => ⟨vs, rfl, SValListDenotes.mono_heaps extOpt extOrig hvs⟩
  | .ptr inner, _, ⟨t, a, wOrig, rfl, ha, hty, hw⟩ =>
    ⟨t, a, wOrig, rfl, extOrig.getElem?_eq ha, hty, SValDenotes.mono_heaps extOpt extOrig (sv := inner) hw⟩

theorem SValListDenotes.mono_heaps {hOpt1 hOpt2 hOrig1 hOrig2 : Heap F} {locOpt : Environment F Nat}
    (extOpt : Heap.Extends hOpt1 hOpt2) (extOrig : Heap.Extends hOrig1 hOrig2) :
    ∀ {svs : List SVal} {vs : List (SourceValue F)},
      SValListDenotes hOpt1 hOrig1 locOpt svs vs → SValListDenotes hOpt2 hOrig2 locOpt svs vs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨hd, tl⟩ =>
    ⟨SValDenotes.mono_heaps extOpt extOrig hd, SValListDenotes.mono_heaps extOpt extOrig tl⟩
  | [], _ :: _, h | _ :: _, [], h => False.elim h

end

/-- Environment denotation: every lookup in `senv` denotes the corresponding lookup in `locOrig`. -/
def EnvDenotes (hOpt hOrig : Heap F) (locOpt : Environment F Nat)
    (senv : SEnv) (locOrig : Environment F Nat) : Prop :=
  ∀ x sv, senv.lookup x = some sv →
    ∃ vOrig, locOrig.find? (·.1 == x) = some (x, vOrig) ∧
      SValDenotes hOpt hOrig locOpt sv vOrig

theorem EnvDenotes.lift {hOpt1 hOpt2 hOrig1 hOrig2 : Heap F}
    {locOpt1 locOpt2 locOrig : Environment F Nat} {c : Nat} {senv : SEnv}
    (extOpt : Heap.Extends hOpt1 hOpt2) (extOrig : Heap.Extends hOrig1 hOrig2)
    (hloc : ∀ y, NotPEGe c y → locOpt2.find? (·.1 == y) = locOpt1.find? (·.1 == y))
    (hnot : SEnvNotPEGe c senv)
    (h : EnvDenotes hOpt1 hOrig1 locOpt1 senv locOrig) :
    EnvDenotes hOpt2 hOrig2 locOpt2 senv locOrig := by
  intro x sv hl
  obtain ⟨vOrig, hf, hsv⟩ := h x sv hl
  exact ⟨vOrig, hf, hsv.lift extOpt extOrig hloc (hnot.lookup hl)⟩

/-- Pointwise lockstep denotation between a static binding list `sbinds` and an original
runtime binding list `origBinds` with identical keys in identical order. -/
def BindsDenote (hOpt hOrig : Heap F) (locOpt : Environment F Nat) :
    SEnv → Environment F Nat → Prop
  | [], [] => True
  | (k1, sv) :: sbs, (k2, v) :: obs =>
      k1 = k2 ∧ SValDenotes hOpt hOrig locOpt sv v ∧ BindsDenote hOpt hOrig locOpt sbs obs
  | _, _ => False

theorem BindsDenote.append {hOpt hOrig : Heap F} {locOpt : Environment F Nat}
    {s1 s2 : SEnv} {o1 o2 : Environment F Nat}
    (h1 : BindsDenote hOpt hOrig locOpt s1 o1) (h2 : BindsDenote hOpt hOrig locOpt s2 o2) :
    BindsDenote hOpt hOrig locOpt (s1 ++ s2) (o1 ++ o2) := by
  induction s1 generalizing o1 with
  | nil => cases o1 with | nil => exact h2 | cons _ _ => exact False.elim h1
  | cons p s1 ih =>
    cases o1 with
    | nil => exact False.elim h1
    | cons q o1 => exact ⟨h1.1, h1.2.1, ih h1.2.2⟩

theorem BindsDenote.extend_env {hOpt hOrig : Heap F} {locOpt locOrig : Environment F Nat}
    {sbinds senv : SEnv} {origBinds : Environment F Nat}
    (hb : BindsDenote hOpt hOrig locOpt sbinds origBinds)
    (he : EnvDenotes hOpt hOrig locOpt senv locOrig) :
    EnvDenotes hOpt hOrig locOpt (sbinds ++ senv) (origBinds ++ locOrig) := by
  intro x sv hl
  induction sbinds generalizing origBinds with
  | nil =>
    cases origBinds with
    | nil => exact he x sv hl
    | cons _ _ => exact False.elim hb
  | cons p sbs ih =>
    rcases p with ⟨k1, sv1⟩
    cases origBinds with
    | nil => exact False.elim hb
    | cons q obs =>
      rcases q with ⟨k2, v2⟩
      obtain ⟨rfl, hsv1, hbtl⟩ := hb
      simp only [List.cons_append, List.lookup, List.find?] at hl ⊢
      cases hkx : (x == k1) with
      | true =>
        rw [hkx] at hl; simp only [Option.some.injEq] at hl; subst hl
        have hxk : k1 = x := (beq_iff_eq.mp hkx).symm
        subst hxk
        simp only [beq_self_eq_true]
        exact ⟨v2, rfl, hsv1⟩
      | false =>
        rw [hkx] at hl
        have hkx' : (k1 == x) = false := by
          cases h2 : (k1 == x) with
          | false => rfl
          | true => rw [beq_iff_eq.mp h2, beq_self_eq_true] at hkx; cases hkx
        rw [hkx']
        exact ih hbtl hl

theorem envDenotes_zip {hOpt hOrig : Heap F} {locOpt : Environment F Nat}
    {ks : List String} {svs : List SVal} {vs : List (SourceValue F)}
    (h : SValListDenotes hOpt hOrig locOpt svs vs) :
    EnvDenotes hOpt hOrig locOpt (ks.zip svs) (ks.zip vs) := by
  have hb : BindsDenote hOpt hOrig locOpt (ks.zip svs) (ks.zip vs) := by
    induction ks generalizing svs vs with
    | nil => trivial
    | cons k ks ih =>
      cases svs with
      | nil => cases vs with | nil => trivial | cons _ _ => exact False.elim h
      | cons sv svs =>
        cases vs with
        | nil => exact False.elim h
        | cons v vs => exact ⟨rfl, h.1, ih h.2⟩
  have hempty : EnvDenotes hOpt hOrig locOpt [] [] := fun _ _ hl => by cases hl
  simpa only [List.append_nil] using hb.extend_env hempty

theorem envDenotes_init {hOpt hOrig : Heap F}
    {ks : List String} {argsOpt argsOrig : List (SourceValue F)}
    (hv : ValEqList hOpt hOrig hOpt.length argsOpt argsOrig)
    (hlen : ks.length = argsOpt.length) :
    EnvDenotes hOpt hOrig (ks.zip argsOpt) (ks.map fun p => (p, SVal.var p)) (ks.zip argsOrig) := by
  intro x sv hl
  have hfind : ∀ (ls : List String) (a1 a2 : List (SourceValue F)),
      ValEqList hOpt hOrig hOpt.length a1 a2 → ls.length = a1.length →
      (ls.map fun p => (p, SVal.var p)).lookup x = some sv →
      ∃ vOpt vOrig,
        (ls.zip a1).find? (·.1 == x) = some (x, vOpt) ∧
        (ls.zip a2).find? (·.1 == x) = some (x, vOrig) ∧
        sv = .var x ∧ ValEq hOpt hOrig hOpt.length vOpt vOrig := by
    intro ls
    induction ls with
    | nil => intro _ _ _ _ hl'; cases hl'
    | cons k ks ih =>
      intro a1 a2 ha hl1 hl'
      cases a1 with
      | nil => cases hl1
      | cons v1 a1 =>
        cases a2 with
        | nil => simp [ValEqList] at ha
        | cons v2 a2 =>
          rw [ValEqList] at ha
          simp only [List.map_cons, List.lookup] at hl'
          simp only [List.zip_cons_cons, List.find?]
          cases hxk : (x == k) with
          | true =>
            rw [hxk] at hl'; simp only [Option.some.injEq] at hl'
            have heq : x = k := beq_iff_eq.mp hxk
            subst heq; subst hl'
            rw [beq_self_eq_true]
            exact ⟨v1, v2, rfl, rfl, rfl, ha.1⟩
          | false =>
            rw [hxk] at hl'
            have hkx : (k == x) = false := by
              cases h2 : (k == x) with
              | false => rfl
              | true => rw [beq_iff_eq.mp h2, beq_self_eq_true] at hxk; cases hxk
            rw [hkx]
            exact ih a1 a2 ha.2 (Nat.succ.inj hl1) hl'
  obtain ⟨vOpt, vOrig, hf1, hf2, rfl, hveq⟩ := hfind ks argsOpt argsOrig hv hlen hl
  exact ⟨vOrig, hf2, vOpt, hf1, hveq⟩

end SValPure

section SValOps

variable {F : Type} [Field F] [DecidableEq F]

/-! ### `reifySVal` Backward Soundness (Zero Original-Heap Allocation!) -/

theorem instanceName_nil (nm : String) :
    SourceSemantics.instanceName [] nm (some []) = nm := rfl

omit [DecidableEq F] in
theorem map_qualifyExpr_map_cast (es : List Expr) :
    (es.map qualifyExpr).map (Aiur.Generic.Expr.map (Nat.cast : Nat → F)) =
      es.map (qualifyExprF F) := by
  simp [List.map_map, Function.comp_def, qualifyExprF]

mutual

theorem evalExprN_reifySVal_backward {wOpt : World F} {d : Nat}
    {locOpt : Environment F Nat} {hOpt1 hOpt2 hOrig : Heap F} :
    ∀ {sv : SVal} {vOrig vOpt : SourceValue F},
      SValDenotes hOpt1 hOrig locOpt sv vOrig →
      EvalExprN wOpt d [] locOpt (qualifyExprF F (reifySVal sv)) hOpt1 vOpt hOpt2 →
      ValEq hOpt2 hOrig hOpt2.length vOpt vOrig
  | .lit n, _, _, ⟨_, rfl⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev
    rw [ValEq]
  | .subLit a b, _, _, ⟨_, _, rfl⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | binary evl evr hop =>
      cases evl; cases evr
      simp only [evalBinOp, Except.ok.injEq] at hop
      subst hop; rw [ValEq]
  | .var y, _, _, ⟨vOpt', hf', hv⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | var hf =>
      rw [hf'] at hf; simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨_, rfl⟩ := hf; exact hv
  | .tuple svs, _, _, ⟨vs, rfl, hvs⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | tuple hargs =>
      rw [map_qualifyExpr_map_cast] at hargs
      rw [ValEq]
      exact evalArgsN_reifySValList_backward hvs hargs
  | .array svs, _, _, ⟨vs, rfl, hvs⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | array hargs =>
      rw [map_qualifyExpr_map_cast] at hargs
      rw [ValEq]
      exact evalArgsN_reifySValList_backward hvs hargs
  | .ctor en c svs, _, _, ⟨vs, rfl, hvs⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Option.map_some, List.map_nil,
      Aiur.Generic.Expr.map] at ev
    cases ev with
    | construct hargs =>
      rw [map_qualifyExpr_map_cast] at hargs
      rw [ValEq, instanceName_nil]
      exact ⟨rfl, rfl, evalArgsN_reifySValList_backward hvs hargs⟩
  | .ptr inner, _, _, ⟨t, a, wOrig, rfl, ha, hty, hw⟩, ev => by
    simp only [reifySVal, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | store evInner =>
      have hwEq := evalExprN_reifySVal_backward hw evInner
      rw [ValEq]
      refine ⟨hwEq.type_eq.trans hty, by simp, _, wOrig, by simp, ha, rfl, hty, ?_⟩
      exact ValEq.mono (Heap.Extends.append_right _ _) (Heap.Extends.refl _) (Nat.le_refl _) hwEq

theorem evalArgsN_reifySValList_backward {wOpt : World F} {d : Nat}
    {locOpt : Environment F Nat} {hOpt1 hOpt2 hOrig : Heap F} :
    ∀ {svs : List SVal} {vsOrig vsOpt : List (SourceValue F)},
      SValListDenotes hOpt1 hOrig locOpt svs vsOrig →
      EvalArgsN wOpt d [] locOpt ((reifySValList svs).map (qualifyExprF F)) hOpt1 vsOpt hOpt2 →
      ValEqList hOpt2 hOrig hOpt2.length vsOpt vsOrig
  | [], [], _, _, ev => by
    cases ev; simp [ValEqList]
  | sv :: svs, v :: vs, _, ⟨hd, tl⟩, ev => by
    simp only [reifySValList, List.map_cons] at ev
    cases ev with
    | cons evHd evTl =>
      have hhd := evalExprN_reifySVal_backward hd evHd
      have tlM := SValListDenotes.mono_heaps evHd.heap_extends (Heap.Extends.refl _) tl
      have htl := evalArgsN_reifySValList_backward tlM evTl
      rw [ValEqList]
      exact ⟨hhd.mono_heaps evTl.heap_extends (Heap.Extends.refl _), htl⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => False.elim h

end

/-! ### Static Pattern Matching (`matchPatSVal`, `selectArmSVal`) Soundness -/

theorem constructorName_named_nil (nm : String) :
    SourceSemantics.constructorName [] (.named nm []) = nm := by
  simp [SourceSemantics.constructorName, Aiur.Generic.Ty.toCore, Aiur.Generic.Instance.symbol]

omit [DecidableEq F] in
theorem subLit_ne_lit (fc : FieldCompatible64 F) {n a b : Nat}
    (hn : n < natLimit) (hab : a < b) (hb : b < natLimit) :
    ((n : F) ≠ (a : F) - (b : F)) := by
  intro heq
  have heq' : ((n + b : Nat) : F) = (a : F) := by
    push_cast
    rw [heq]; ring
  have h1 : n + b < fieldBound64 := by unfold natLimit fieldBound64 at *; omega
  have h2 : a < fieldBound64 := by unfold natLimit fieldBound64 at *; omega
  have := fc.natCast_inj h1 h2 heq'
  omega

omit [Field F] [DecidableEq F] in
theorem matchListWith_attach {B : Type}
    (f : B → SourceValue F → Except EvalError (Option (Environment F Nat)))
    (bs : List B) (vs : List (SourceValue F)) :
    matchListWith (fun pat value => f pat.val value) bs.attach vs =
      matchListWith f bs vs := by
  induction bs generalizing vs with
  | nil => cases vs <;> rfl
  | cons b bs ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [List.attach_cons, matchListWith]
      have hmap :
          matchListWith (fun (pat : {x // x ∈ b :: bs}) value => f pat.val value)
            (bs.attach.map fun x => ⟨x.val, List.mem_cons_of_mem _ x.property⟩) vs =
          matchListWith (fun (pat : {x // x ∈ bs}) value => f pat.val value)
            bs.attach vs := by
        clear ih
        generalize bs.attach = xs
        induction xs generalizing vs with
        | nil => cases vs <;> rfl
        | cons a as iha =>
          cases vs with
          | nil => rfl
          | cons u us => simp only [List.map_cons, matchListWith, iha]
      rw [hmap, ih]

omit [Field F] [DecidableEq F] in
theorem matchListWith_map_attach {A B : Type}
    (f : B → SourceValue F → Except EvalError (Option (Environment F Nat)))
    (g : A → B) (ps : List A) (vs : List (SourceValue F)) :
    matchListWith (fun pat value => f pat.val value) (ps.map g).attach vs =
      matchListWith (fun a value => f (g a) value) ps vs := by
  rw [matchListWith_attach]
  induction ps generalizing vs with
  | nil => cases vs <;> rfl
  | cons p ps ih =>
    cases vs with
    | nil => rfl
    | cons v vs => simp only [List.map_cons, matchListWith, ih]

omit [DecidableEq F] in
theorem map_qualifyPat_map_cast (ps : List Pat) :
    (ps.map qualifyPat).map (Aiur.Generic.Pattern.map (Nat.cast : Nat → F)) =
      ps.map (qualifyPatF F) := by
  simp [List.map_map, Function.comp_def, qualifyPatF]

mutual

theorem matchPatSVal_sound (fc : FieldCompatible64 F) (w : World F)
    {hOpt hOrig : Heap F} {locOpt : Environment F Nat} :
    ∀ (p : Pat) (sv : SVal) (vOrig : SourceValue F),
      SValDenotes hOpt hOrig locOpt sv vOrig →
      match matchPatSVal p sv with
      | .matched sbinds =>
          ∃ origBinds, w.matchPattern [] hOrig (qualifyPatF F p) vOrig = .ok (some origBinds) ∧
            BindsDenote hOpt hOrig locOpt sbinds origBinds
      | .noMatch =>
          w.matchPattern [] hOrig (qualifyPatF F p) vOrig = .ok none
      | .unknown => True
  | .wildcard, _, _, _ =>
    ⟨[], by simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith], trivial⟩
  | .bind x, sv, vOrig, hsv =>
    ⟨[(x, vOrig)],
      by simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith],
      ⟨rfl, hsv, trivial⟩⟩
  | .literal n, .lit m, vOrig, ⟨hm, hv⟩ => by
    subst hv
    unfold matchPatSVal
    by_cases hlt : (n < natLimit && m < natLimit) = true
    · simp only [hlt, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
      by_cases heq : (n == m) = true
      · simp only [heq, ↓reduceIte]
        have hnm : n = m := beq_iff_eq.mp heq
        subst hnm
        exact ⟨[], by simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
          World.matchPattern, matchPatternWith, Aiur.Pattern.bindings], trivial⟩
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        have hne : (n : F) ≠ (m : F) := fun h => by
          have := fc.natCast_inj56 hlt.1 hlt.2 h
          rw [this, beq_self_eq_true] at heq; exact heq rfl
        simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
          World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, hne]
    · simp [hlt]
  | .literal n, .subLit a b, vOrig, ⟨hab, hb, hv⟩ => by
    subst hv
    unfold matchPatSVal
    by_cases hcond : (n < natLimit && a < b && b < natLimit) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hne := subLit_ne_lit fc hcond.1.1 hcond.1.2 hcond.2
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
        World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, hne]
    · simp [hcond]
  | .literal _, .var _, _, _ => trivial
  | .literal _, .tuple _, vOrig, ⟨_, hv, _⟩
  | .literal _, .array _, vOrig, ⟨_, hv, _⟩
  | .literal _, .ctor _ _ _, vOrig, ⟨_, hv, _⟩
  | .literal _, .ptr _, vOrig, ⟨_, _, _, hv, _, _, _⟩ => by
    subst hv
    simp [matchPatSVal, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
      World.matchPattern, matchPatternWith, Aiur.Pattern.bindings]
  | .tuple ps, .tuple svs, vOrig, ⟨vs, hv, hvs⟩
  | .tuple ps, .array svs, vOrig, ⟨vs, hv, hvs⟩
  | .array ps, .tuple svs, vOrig, ⟨vs, hv, hvs⟩
  | .array ps, .array svs, vOrig, ⟨vs, hv, hvs⟩ => by
    subst hv
    unfold matchPatSVal
    have hlen : svs.length = vs.length := svalListDenotes_length_eq hvs
    by_cases hpeq : (ps.length == svs.length) = true
    · simp only [hpeq, ↓reduceIte]
      have hplen : ps.length = vs.length := (beq_iff_eq.mp hpeq).trans hlen
      have ih := matchPatListSVal_sound fc w ps svs vs hvs
      cases hm : matchPatListSVal ps svs with
      | matched sbinds =>
        rw [hm] at ih; dsimp only at ih
        obtain ⟨obs, hml, hbd⟩ := ih
        refine ⟨obs, ?_, hbd⟩
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, List.length_map, hplen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [map_qualifyPat_map_cast, matchListWith_map_attach]
        exact hml
      | noMatch =>
        rw [hm] at ih; dsimp only at ih
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, List.length_map, hplen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [map_qualifyPat_map_cast, matchListWith_map_attach]
        exact ih
      | unknown => trivial
    · simp only [hpeq, Bool.false_eq_true, ↓reduceIte]
      have hne : (ps.length != vs.length) = true := by
        rw [← hlen]; simp [bne, hpeq]
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, hne]
  | .tuple _, .var _, _, _ | .array _, .var _, _, _ => trivial
  | .tuple _, .lit _, vOrig, ⟨_, hv⟩ | .tuple _, .subLit _ _, vOrig, ⟨_, _, hv⟩
  | .tuple _, .ctor _ _ _, vOrig, ⟨_, hv, _⟩ | .tuple _, .ptr _, vOrig, ⟨_, _, _, hv, _, _, _⟩
  | .array _, .lit _, vOrig, ⟨_, hv⟩ | .array _, .subLit _ _, vOrig, ⟨_, _, hv⟩
  | .array _, .ctor _ _ _, vOrig, ⟨_, hv, _⟩ | .array _, .ptr _, vOrig, ⟨_, _, _, hv, _, _, _⟩ => by
    subst hv
    simp [matchPatSVal, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
      World.matchPattern, matchPatternWith]
  | .construct ty c ps, sv, vOrig, hsv => by
    cases ty with
    | named tyNm targs =>
      cases targs with
      | nil =>
        cases sv with
        | ctor ty' c' svs =>
          rcases hsv with ⟨vs, rfl, hvs⟩
          unfold matchPatSVal
          have hlen := svalListDenotes_length_eq hvs
          by_cases hcond : (qualifyName tyNm == qualifyName ty' && c == c' && ps.length == svs.length) = true
          · simp only [hcond, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨⟨hty, hc⟩, hplen⟩ := hcond
            have hplen' : ps.length = vs.length := hplen.trans hlen
            have ih := matchPatListSVal_sound fc w ps svs vs hvs
            cases hm : matchPatListSVal ps svs with
            | matched sbinds =>
              rw [hm] at ih; dsimp only at ih
              obtain ⟨obs, hml, hbd⟩ := ih
              refine ⟨obs, ?_, hbd⟩
              simp only [qualifyPatF, qualifyPat, qualifyTy, Aiur.Generic.Pattern.map,
                World.matchPattern, matchPatternWith, List.map_nil, constructorName_named_nil,
                List.length_map, hty, hc, hplen', bne_self_eq_false, Bool.or_self,
                Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
              rw [map_qualifyPat_map_cast, matchListWith_map_attach]
              exact hml
            | noMatch =>
              rw [hm] at ih; dsimp only at ih
              simp only [qualifyPatF, qualifyPat, qualifyTy, Aiur.Generic.Pattern.map,
                World.matchPattern, matchPatternWith, List.map_nil, constructorName_named_nil,
                List.length_map, hty, hc, hplen', bne_self_eq_false, Bool.or_self,
                Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
              rw [map_qualifyPat_map_cast, matchListWith_map_attach]
              exact ih
            | unknown => trivial
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
            have hor : (qualifyName ty' != qualifyName tyNm || c' != c || ps.length != vs.length) = true := by
              rw [← hlen]
              by_cases h1 : qualifyName tyNm = qualifyName ty'
              · by_cases h2 : c = c'
                · by_cases h3 : ps.length = svs.length
                  · simp [h1, h2, h3] at hcond
                  · simp [bne, h3]
                · simp [bne, Ne.symm h2]
              · simp [bne, Ne.symm h1]
            simp [qualifyPatF, qualifyPat, qualifyTy, Aiur.Generic.Pattern.map,
              World.matchPattern, matchPatternWith, constructorName_named_nil, hor]
        | var _ => trivial
        | lit _ =>
          rcases hsv with ⟨_, rfl⟩
          simp [matchPatSVal, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
            World.matchPattern, matchPatternWith]
        | subLit _ _ =>
          rcases hsv with ⟨_, _, rfl⟩
          simp [matchPatSVal, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
            World.matchPattern, matchPatternWith]
        | tuple _ | array _ =>
          rcases hsv with ⟨_, rfl, _⟩
          simp [matchPatSVal, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
            World.matchPattern, matchPatternWith]
        | ptr _ =>
          rcases hsv with ⟨_, _, _, rfl, _, _, _⟩
          simp [matchPatSVal, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
            World.matchPattern, matchPatternWith]
      | cons _ _ => simp [matchPatSVal]
    | _ => simp [matchPatSVal]
  | .global _ _, _, _, _ | .orElse _ _ _, _, _, _ | .load _, _, _, _
  | .repeat _ _, _, _, _ | .record _ _, _, _, _ | .constructAs _ _ _ _, _, _, _ => by
    simp [matchPatSVal]
termination_by p _ _ _ => sizeOf p

theorem matchPatListSVal_sound (fc : FieldCompatible64 F) (w : World F)
    {hOpt hOrig : Heap F} {locOpt : Environment F Nat} :
    ∀ (ps : List Pat) (svs : List SVal) (vsOrig : List (SourceValue F)),
      SValListDenotes hOpt hOrig locOpt svs vsOrig →
      match matchPatListSVal ps svs with
      | .matched sbinds =>
          ∃ origBinds,
            matchListWith (fun p value => w.matchPattern [] hOrig (qualifyPatF F p) value)
              ps vsOrig = .ok (some origBinds) ∧
            BindsDenote hOpt hOrig locOpt sbinds origBinds
      | .noMatch =>
          matchListWith (fun p value => w.matchPattern [] hOrig (qualifyPatF F p) value)
            ps vsOrig = .ok none
      | .unknown => True
  | [], [], [], _ =>
    ⟨[], by simp [matchListWith, pure, Except.pure], trivial⟩
  | p :: ps, sv :: svs, v :: vs, ⟨hd, tl⟩ => by
    unfold matchPatListSVal
    have ih1 := matchPatSVal_sound fc w p sv v hd
    cases h1 : matchPatSVal p sv with
    | noMatch =>
      rw [h1] at ih1; dsimp only at ih1 ⊢
      unfold matchListWith; simp [ih1, bind, Except.bind]
    | unknown => trivial
    | matched b1 =>
      rw [h1] at ih1; dsimp only at ih1 ⊢
      obtain ⟨ob1, hm1, hb1⟩ := ih1
      have ih2 := matchPatListSVal_sound fc w ps svs vs tl
      cases h2 : matchPatListSVal ps svs with
      | noMatch =>
        rw [h2] at ih2; dsimp only at ih2 ⊢
        unfold matchListWith; simp [hm1, ih2, bind, Except.bind]
      | unknown => trivial
      | matched b2 =>
        rw [h2] at ih2; dsimp only at ih2 ⊢
        obtain ⟨ob2, hm2, hb2⟩ := ih2
        refine ⟨ob1 ++ ob2, ?_, hb1.append hb2⟩
        unfold matchListWith; simp [hm1, hm2, bind, Except.bind]
  | [], _ :: _, _ :: _, _ => by simp [matchPatListSVal, matchListWith, pure, Except.pure]
  | _ :: _, [], [], _ => by simp [matchPatListSVal, matchListWith, pure, Except.pure]
  | _, [], _ :: _, h | _, _ :: _, [], h => False.elim h
termination_by ps _ _ _ => sizeOf ps

end

theorem selectArmSVal_sound (fc : FieldCompatible64 F) (w : World F)
    {hOpt hOrig : Heap F} {locOpt : Environment F Nat}
    {sv : SVal} {vOrig : SourceValue F} {arms : List (Pat × Expr)}
    {sbinds : SEnv} {armBody : Expr}
    (hsv : SValDenotes hOpt hOrig locOpt sv vOrig)
    (hsel : selectArmSVal sv arms = some (sbinds, armBody)) :
    ∃ origBinds,
      SourceSemantics.selectArm w [] hOrig vOrig
        (arms.map fun (p, b) => (qualifyPatF F p, qualifyExprF F b)) =
          .ok (some (origBinds, qualifyExprF F armBody)) ∧
      BindsDenote hOpt hOrig locOpt sbinds origBinds := by
  induction arms with
  | nil => cases hsel
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    unfold selectArmSVal at hsel
    have hm := matchPatSVal_sound fc w p sv vOrig hsv
    cases h1 : matchPatSVal p sv with
    | matched bs =>
      rw [h1] at hsel hm; dsimp only at hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      obtain ⟨obs, hmp, hbd⟩ := hm
      refine ⟨obs, ?_, hbd⟩
      simp [SourceSemantics.selectArm, hmp, bind, Except.bind]
    | noMatch =>
      rw [h1] at hsel hm; dsimp only at hm
      obtain ⟨obs, hsel', hbd⟩ := ih hsel
      refine ⟨obs, ?_, hbd⟩
      simp [SourceSemantics.selectArm, hm, hsel', bind, Except.bind]
    | unknown => rw [h1] at hsel; cases hsel

/-! ### `freshPat` Pattern-Matching Lockstep Soundness -/

mutual

theorem matchPattern_binds_inRange_aux {w : World F} {h : Heap F} {lo hi : Nat} :
    ∀ {p : Pat} {v : SourceValue F} {bs : Environment F Nat},
      PatBindsInRange lo hi p →
      w.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) →
      ∀ kv ∈ bs, ∃ n, lo ≤ n ∧ n < hi ∧ kv.1 = peVarName n
  | .bind y, v, bs, ⟨n, hn1, hn2, hy⟩, hm => by
    subst hy
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm
    intro kv hkv; simp only [List.mem_singleton] at hkv; subst hkv
    exact ⟨n, hn1, hn2, rfl⟩
  | .wildcard, _, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; intro _ hmem; cases hmem
  | .literal x, v, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
    cases v with
    | field y =>
      simp only [Aiur.Pattern.bindings] at hm
      split at hm
      · simp only [Option.some.injEq] at hm; subst hm; intro _ hmem; cases hmem
      · cases hm
    | _ => simp [Aiur.Pattern.bindings] at hm
  | .tuple ps, v, bs, hps, hm | .array ps, v, bs, hps, hm => by
    cases v with
    | tuple vs =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith] at hm
      split at hm
      · cases hm
      · rw [map_qualifyPat_map_cast, matchListWith_map_attach] at hm
        exact matchList_binds_inRange_aux ps vs hps hm
    | _ => simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith] at hm
  | .construct ty c ps, v, bs, hps, hm => by
    cases v with
    | construct en c' vs =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith] at hm
      split at hm
      · cases hm
      · rw [map_qualifyPat_map_cast, matchListWith_map_attach] at hm
        exact matchList_binds_inRange_aux ps vs hps hm
    | _ => simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith] at hm
  | .global _ _, _, _, h, _ | .orElse _ _ _, _, _, h, _ | .load _, _, _, h, _
  | .repeat _ _, _, _, h, _ | .record _ _, _, _, h, _ | .constructAs _ _ _ _, _, _, h, _ =>
    False.elim h

theorem matchList_binds_inRange_aux {w : World F} {h : Heap F} {lo hi : Nat} :
    ∀ (ps : List Pat) (vs : List (SourceValue F)) {bs : Environment F Nat},
      PatListBindsInRange lo hi ps →
      matchListWith (fun p value => w.matchPattern [] h (qualifyPatF F p) value)
        ps vs = .ok (some bs) →
      ∀ kv ∈ bs, ∃ n, lo ≤ n ∧ n < hi ∧ kv.1 = peVarName n
  | [], [], _, _, hm => by
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; intro _ hmem; cases hmem
  | p :: ps, v :: vs, _, ⟨hp, hps⟩, hm => by
    unfold matchListWith at hm
    cases h1 : w.matchPattern [] h (qualifyPatF F p) v with
    | error e => simp [h1, bind, Except.bind] at hm
    | ok opt1 =>
      simp only [h1, bind, Except.bind] at hm
      cases opt1 with
      | none => simp at hm
      | some b1 =>
        cases h2 : matchListWith (fun p value => w.matchPattern [] h (qualifyPatF F p) value) ps vs with
        | error e => simp [h2] at hm
        | ok opt2 =>
          simp only [h2] at hm
          cases opt2 with
          | none => simp at hm
          | some b2 =>
            simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
            subst hm
            intro kv hkv
            rcases List.mem_append.mp hkv with hmem1 | hmem2
            · exact matchPattern_binds_inRange_aux hp h1 kv hmem1
            · exact matchList_binds_inRange_aux ps vs hps h2 kv hmem2
  | [], _ :: _, _, _, hm | _ :: _, [], _, _, hm => by
    simp [matchListWith, pure, Except.pure] at hm

end

omit [Field F] [DecidableEq F] in
theorem find?_append_skip_of_binds_inRange {lo hi : Nat} {bs loc : Environment F Nat}
    (hbs : ∀ kv ∈ bs, ∃ n, lo ≤ n ∧ n < hi ∧ kv.1 = peVarName n)
    {y : String} (hy : NotPEGe lo y) :
    (bs ++ loc).find? (·.1 == y) = loc.find? (·.1 == y) := by
  induction bs with
  | nil => rfl
  | cons kv bs ih =>
    simp only [List.cons_append, List.find?]
    obtain ⟨n, hn, _, hkv⟩ := hbs kv List.mem_cons_self
    have hne : (kv.1 == y) = false := by
      cases h : (kv.1 == y) with
      | false => rfl
      | true =>
        have : y = peVarName n := (beq_iff_eq.mp h).symm.trans hkv
        exact absurd this (hy n hn)
    rw [hne]
    exact ih (fun q hq => hbs q (List.mem_cons_of_mem _ hq))

omit [Field F] [DecidableEq F] in
theorem freshPatList_length (ps : List Pat) (st : PEState) :
    (freshPatList ps st).1.1.length = ps.length := by
  induction ps generalizing st with
  | nil => rfl
  | cons q qs ih =>
    rw [freshPatList]
    rcases _ : freshPat q st with ⟨⟨q', b1⟩, st1⟩
    have := ih st1
    rcases _ : freshPatList qs st1 with ⟨⟨qs', b2⟩, st2⟩
    simpa using this

omit [Field F] [DecidableEq F] in
theorem find?_append_of_some {α : Type} {p : α → Bool} {xs ys : List α} {a : α}
    (h : xs.find? p = some a) : (xs ++ ys).find? p = some a := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.cons_append, List.find?] at h ⊢
    cases hpx : p x with
    | true => rw [hpx] at h; exact h
    | false => rw [hpx] at h; exact ih h

-- Matching the alpha-renamed pattern `p'` from `freshPat p st` on `vOpt` mirrors matching `p`
-- on `vOrig` (when `ValEq vOpt vOrig`), and `pBinds` denotes `origBinds` in any `locExt`
-- preserving every binding in `optBinds` within `[st.nextId, st'.nextId)`.
mutual

theorem freshPat_matchPattern_sound {wOpt wOrig : World F} {hOpt hOrig : Heap F}
    (haux : SameAuxWorld wOpt wOrig) :
    ∀ (p : Pat) (st : PEState) (vOpt vOrig : SourceValue F)
      (optRes : Option (Environment F Nat)),
      isSimplePat p = true →
      ValEq hOpt hOrig hOpt.length vOpt vOrig →
      wOpt.matchPattern [] hOpt (qualifyPatF F (freshPat p st).1.1) vOpt = .ok optRes →
      match optRes with
      | none => wOrig.matchPattern [] hOrig (qualifyPatF F p) vOrig = .ok none
      | some optBinds =>
          ∃ origBinds,
            wOrig.matchPattern [] hOrig (qualifyPatF F p) vOrig = .ok (some origBinds) ∧
            (∀ kv ∈ optBinds, ∃ n, st.nextId ≤ n ∧ n < (freshPat p st).2.nextId ∧ kv.1 = peVarName n) ∧
            ∀ (locExt : Environment F Nat),
              (∀ n v, st.nextId ≤ n → n < (freshPat p st).2.nextId →
                optBinds.find? (·.1 == peVarName n) = some (peVarName n, v) →
                locExt.find? (·.1 == peVarName n) = some (peVarName n, v)) →
              BindsDenote hOpt hOrig locExt (freshPat p st).1.2 origBinds
  | .bind x, st, vOpt, vOrig, optRes, _, hv, hm => by
    simp only [freshPat, allocFresh, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
      World.matchPattern, matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    refine ⟨[(x, vOrig)], by simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
      World.matchPattern, matchPatternWith], ?_, ?_⟩
    · intro kv hkv; simp only [List.mem_singleton] at hkv; subst hkv
      exact ⟨st.nextId, Nat.le_refl _, Nat.lt_succ_self _, rfl⟩
    · intro locExt hloc
      refine ⟨rfl, ?_, trivial⟩
      refine ⟨vOpt, ?_, hv⟩
      exact hloc st.nextId vOpt (Nat.le_refl _) (Nat.lt_succ_self _) (by simp [List.find?])
  | .wildcard, st, vOpt, vOrig, optRes, _, _, hm => by
    simp only [freshPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
      World.matchPattern, matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    exact ⟨[], by simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
      World.matchPattern, matchPatternWith], (fun _ h => by cases h), fun _ _ => trivial⟩
  | .literal n, st, vOpt, vOrig, optRes, _, hv, hm => by
    simp only [freshPat] at hm ⊢
    have htr := matchPatternWith_valEq wOpt.constant wOpt.constDepth [] (qualifyPatF F (.literal n))
      vOpt vOrig optRes hv hm
    cases optRes with
    | none =>
      unfold World.matchPattern
      rw [← haux.constant_eq, ← haux.constDepth_eq]; exact htr
    | some optBinds =>
      obtain ⟨origBinds, hmOrig, hEq⟩ := htr
      have hnil : optBinds = [] := by
        cases vOpt with
        | field y =>
          simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
            matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.ok.injEq] at hm
          split at hm
          · simp only [Option.some.injEq] at hm; exact hm.symm
          · cases hm
        | _ => simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, Aiur.Pattern.bindings] at hm
      subst hnil
      have hnil2 : origBinds = [] := by
        cases origBinds with
        | nil => rfl
        | cons _ _ => cases hEq.1
      subst hnil2
      exact ⟨[], by unfold World.matchPattern; rw [← haux.constant_eq, ← haux.constDepth_eq]; exact hmOrig,
        (fun _ h => by cases h), fun _ _ => trivial⟩
  | .tuple ps, st, vOpt, vOrig, optRes, hp, hv, hm
  | .array ps, st, vOpt, vOrig, optRes, hp, hv, hm => by
    unfold freshPat at hm ⊢
    rcases hf : freshPatList ps st with ⟨⟨ps', bs⟩, st'⟩
    rw [hf] at hm; dsimp only at hm ⊢
    cases vOpt with
    | tuple xsOpt =>
      cases vOrig with
      | tuple xsOrig =>
        rw [ValEq] at hv
        have hlenPs : ps'.length = ps.length := by
          have := freshPatList_length ps st
          rw [hf] at this; exact this
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, List.length_map] at hm
        rw [hlenPs] at hm
        split at hm
        · next hne =>
          simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
          have hne' : (ps.length != xsOrig.length) = true := by rw [← hv.length_eq]; exact hne
          simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
            matchPatternWith, hne']
        · next hne =>
          have hne' : ¬ (ps.length != xsOrig.length) = true := by rw [← hv.length_eq]; exact hne
          rw [map_qualifyPat_map_cast, matchListWith_map_attach] at hm
          have ih := freshPatList_matchPattern_sound haux ps st xsOpt xsOrig optRes hp hv
            (by rw [hf]; exact hm)
          rw [hf] at ih; dsimp only at ih
          cases optRes with
          | none =>
            simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
              matchPatternWith, List.length_map, hne']
            rw [map_qualifyPat_map_cast, matchListWith_map_attach]
            exact ih
          | some optBinds =>
            obtain ⟨origBinds, hmOrig, hrange, hbd⟩ := ih
            refine ⟨origBinds, ?_, hrange, hbd⟩
            simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
              matchPatternWith, List.length_map, hne']
            rw [map_qualifyPat_map_cast, matchListWith_map_attach]
            exact hmOrig
      | _ => simp [ValEq] at hv
    | field _ =>
      cases vOrig with
      | field _ =>
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
      | _ => simp [ValEq] at hv
    | construct _ _ _ =>
      cases vOrig with
      | construct _ _ _ =>
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases vOrig with
      | ptr _ _ =>
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
      | _ => simp [ValEq] at hv
  | .construct ty c ps, st, vOpt, vOrig, optRes, hp, hv, hm => by
    unfold freshPat at hm ⊢
    rcases hf : freshPatList ps st with ⟨⟨ps', bs⟩, st'⟩
    rw [hf] at hm; dsimp only at hm ⊢
    cases vOpt with
    | construct en1 c1 xsOpt =>
      cases vOrig with
      | construct en2 c2 xsOrig =>
        rw [ValEq] at hv
        obtain ⟨rfl, rfl, hxs⟩ := hv
        have hlenPs : ps'.length = ps.length := by
          have := freshPatList_length ps st
          rw [hf] at this; exact this
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, List.length_map] at hm
        rw [hlenPs] at hm
        split at hm
        · next hne =>
          simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
          have hne' : (en1 != constructorName [] (qualifyTy ty) || c1 != c || ps.length != xsOrig.length) = true := by
            rw [← hxs.length_eq]; exact hne
          simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
            matchPatternWith, hne']
        · next hne =>
          have hne' : ¬ (en1 != constructorName [] (qualifyTy ty) || c1 != c || ps.length != xsOrig.length) = true := by
            rw [← hxs.length_eq]; exact hne
          rw [map_qualifyPat_map_cast, matchListWith_map_attach] at hm
          have ih := freshPatList_matchPattern_sound haux ps st xsOpt xsOrig optRes hp hxs
            (by rw [hf]; exact hm)
          rw [hf] at ih; dsimp only at ih
          cases optRes with
          | none =>
            simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
              matchPatternWith, List.length_map, hne']
            rw [map_qualifyPat_map_cast, matchListWith_map_attach]
            exact ih
          | some optBinds =>
            obtain ⟨origBinds, hmOrig, hrange, hbd⟩ := ih
            refine ⟨origBinds, ?_, hrange, hbd⟩
            simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
              matchPatternWith, List.length_map, hne']
            rw [map_qualifyPat_map_cast, matchListWith_map_attach]
            exact hmOrig
      | _ => simp [ValEq] at hv
    | field _ =>
      cases vOrig with
      | field _ =>
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
      | _ => simp [ValEq] at hv
    | tuple _ =>
      cases vOrig with
      | tuple _ =>
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
      | _ => simp [ValEq] at hv
    | ptr _ _ =>
      cases vOrig with
      | ptr _ _ =>
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
        subst hm; simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
      | _ => simp [ValEq] at hv
  | .global _ _, _, _, _, _, hp, _, _ | .orElse _ _ _, _, _, _, _, hp, _, _
  | .load _, _, _, _, _, hp, _, _ | .repeat _ _, _, _, _, _, hp, _, _
  | .record _ _, _, _, _, _, hp, _, _ | .constructAs _ _ _ _, _, _, _, _, hp, _, _ => by
    cases hp

theorem freshPatList_matchPattern_sound {wOpt wOrig : World F} {hOpt hOrig : Heap F}
    (haux : SameAuxWorld wOpt wOrig) :
    ∀ (ps : List Pat) (st : PEState) (vsOpt vsOrig : List (SourceValue F))
      (optRes : Option (Environment F Nat)),
      isSimplePatList ps = true →
      ValEqList hOpt hOrig hOpt.length vsOpt vsOrig →
      matchListWith (fun p value => wOpt.matchPattern [] hOpt (qualifyPatF F p) value)
        (freshPatList ps st).1.1 vsOpt = .ok optRes →
      match optRes with
      | none =>
          matchListWith (fun p value => wOrig.matchPattern [] hOrig (qualifyPatF F p) value)
            ps vsOrig = .ok none
      | some optBinds =>
          ∃ origBinds,
            matchListWith (fun p value => wOrig.matchPattern [] hOrig (qualifyPatF F p) value)
              ps vsOrig = .ok (some origBinds) ∧
            (∀ kv ∈ optBinds, ∃ n, st.nextId ≤ n ∧ n < (freshPatList ps st).2.nextId ∧ kv.1 = peVarName n) ∧
            ∀ (locExt : Environment F Nat),
              (∀ n v, st.nextId ≤ n → n < (freshPatList ps st).2.nextId →
                optBinds.find? (·.1 == peVarName n) = some (peVarName n, v) →
                locExt.find? (·.1 == peVarName n) = some (peVarName n, v)) →
              BindsDenote hOpt hOrig locExt (freshPatList ps st).1.2 origBinds
  | [], st, [], [], optRes, _, _, hm => by
    simp only [freshPatList, matchListWith, pure, Except.pure, Except.ok.injEq] at hm
    subst hm
    exact ⟨[], by simp [matchListWith], (fun _ h => by cases h), fun _ _ => trivial⟩
  | p :: ps, st, vOpt :: vsOpt, vOrig :: vsOrig, optRes, hp, hvs, hm => by
    simp only [isSimplePatList, Bool.and_eq_true] at hp
    rw [ValEqList] at hvs
    rw [freshPatList] at hm ⊢
    have hfp1 := freshPat_props p st hp.1
    rcases hf1 : freshPat p st with ⟨⟨p', b1⟩, st1⟩
    rw [hf1] at hfp1 hm; dsimp only at hfp1 hm ⊢
    have hfp2 := freshPatList_props ps st1 hp.2
    rcases hf2 : freshPatList ps st1 with ⟨⟨ps', b2⟩, st2⟩
    rw [hf2] at hfp2 hm; dsimp only at hfp2 hm ⊢
    unfold matchListWith at hm
    cases h1 : wOpt.matchPattern [] hOpt (qualifyPatF F p') vOpt with
    | error e => simp [h1, bind, Except.bind] at hm
    | ok opt1 =>
      simp only [h1, bind, Except.bind] at hm
      cases opt1 with
      | none =>
        simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
        have h1' := freshPat_matchPattern_sound haux p st vOpt vOrig none hp.1 hvs.1 (by rw [hf1]; exact h1)
        unfold matchListWith; simp [h1', bind, Except.bind]
      | some ob1 =>
        have ih1 := freshPat_matchPattern_sound haux p st vOpt vOrig (some ob1) hp.1 hvs.1
          (by rw [hf1]; exact h1)
        rw [hf1] at ih1; dsimp only at ih1
        obtain ⟨orig1, hm1', hr1, hbd1⟩ := ih1
        cases h2 : matchListWith (fun q value => wOpt.matchPattern [] hOpt (qualifyPatF F q) value)
            ps' vsOpt with
        | error e => simp [h2] at hm
        | ok opt2 =>
          simp only [h2] at hm
          cases opt2 with
          | none =>
            simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
            have h2' := freshPatList_matchPattern_sound haux ps st1 vsOpt vsOrig none hp.2 hvs.2
              (by rw [hf2]; exact h2)
            unfold matchListWith; simp [hm1', h2', bind, Except.bind]
          | some ob2 =>
            simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
            have ih2 := freshPatList_matchPattern_sound haux ps st1 vsOpt vsOrig (some ob2) hp.2 hvs.2
              (by rw [hf2]; exact h2)
            rw [hf2] at ih2; dsimp only at ih2
            obtain ⟨orig2, hm2', hr2, hbd2⟩ := ih2
            refine ⟨orig1 ++ orig2, by unfold matchListWith; simp [hm1', hm2', bind, Except.bind], ?_, ?_⟩
            · intro kv hkv
              rcases List.mem_append.mp hkv with hmem1 | hmem2
              · obtain ⟨n, hn1, hn2, hEq⟩ := hr1 kv hmem1
                exact ⟨n, hn1, Nat.lt_of_lt_of_le hn2 hfp2.1, hEq⟩
              · obtain ⟨n, hn1, hn2, hEq⟩ := hr2 kv hmem2
                exact ⟨n, Nat.le_trans hfp1.1 hn1, hn2, hEq⟩
            · intro locExt hloc
              refine (hbd1 locExt ?_).append (hbd2 locExt ?_)
              · intro n v hn1 hn2 hf1'
                exact hloc n v hn1 (Nat.lt_of_lt_of_le hn2 hfp2.1) (find?_append_of_some hf1')
              · intro n v hn1 hn2 hf2'
                apply hloc n v (Nat.le_trans hfp1.1 hn1) hn2
                clear h1 hbd1 hloc
                induction ob1 with
                | nil => exact hf2'
                | cons kv tl ihob =>
                  simp only [List.cons_append, List.find?]
                  obtain ⟨m, _, hm2, hEq⟩ := hr1 kv List.mem_cons_self
                  have hne : (kv.1 == peVarName n) = false := by
                    cases hb : (kv.1 == peVarName n) with
                    | false => rfl
                    | true =>
                      have := peVarName_inj (hEq.symm.trans (beq_iff_eq.mp hb))
                      omega
                  rw [hne]
                  exact ihob (fun q hq => hr1 q (List.mem_cons_of_mem _ hq))
  | [], _, [], _ :: _, _, _, hvs, _ | [], _, _ :: _, [], _, _, hvs, _
  | _ :: _, _, [], _ :: _, _, _, hvs, _ | _ :: _, _, _ :: _, [], _, _, hvs, _ => by
    simp [ValEqList] at hvs
  | [], _, _ :: _, _ :: _, optRes, _, _, hm => by
    simp only [freshPatList, matchListWith, pure, Except.pure, Except.ok.injEq] at hm
    subst hm; rfl
  | p :: ps, st, [], [], optRes, _, _, hm => by
    rw [freshPatList] at hm
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq] at hm
    subst hm; rfl

end

/-! ### Residual ANF Prefix Evaluation (`EvalLetsN`, `wrapLets`, `wrapLetsTail`) -/

/-- Depth-bounded evaluation of a sequence of emitted residual ANF bindings `LetBinds`. -/
inductive EvalLetsN (w : World F) (d : Nat) :
    Environment F Nat → LetBinds → Heap F → Environment F Nat → Heap F → Prop where
  | nil {loc : Environment F Nat} {h : Heap F} :
      EvalLetsN w d loc [] h loc h
  | cons {loc0 loc1 : Environment F Nat} {p : Pat} {rhs : Expr} {rest : LetBinds}
      {h0 hM h1 : Heap F} {v : SourceValue F} {bs : Environment F Nat}
      (evRhs : EvalExprN w d [] loc0 (qualifyExprF F rhs) h0 v hM)
      (hMatch : w.matchPattern [] hM (qualifyPatF F p) v = .ok (some bs))
      (evRest : EvalLetsN w d (bs ++ loc0) rest hM loc1 h1) :
      EvalLetsN w d loc0 ((p, rhs) :: rest) h0 loc1 h1

theorem EvalLetsN.heap_extends {w : World F} {d : Nat}
    {loc0 loc1 : Environment F Nat} {bs : LetBinds} {h0 h1 : Heap F}
    (ev : EvalLetsN w d loc0 bs h0 loc1 h1) : Heap.Extends h0 h1 := by
  induction ev with
  | nil => exact Heap.Extends.refl _
  | cons evRhs _ _ ih => exact evRhs.heap_extends.trans ih

theorem EvalLetsN.append {w : World F} {d : Nat}
    {loc0 loc1 loc2 : Environment F Nat} {b1 b2 : LetBinds} {h0 h1 h2 : Heap F}
    (e1 : EvalLetsN w d loc0 b1 h0 loc1 h1)
    (e2 : EvalLetsN w d loc1 b2 h1 loc2 h2) :
    EvalLetsN w d loc0 (b1 ++ b2) h0 loc2 h2 := by
  induction e1 with
  | nil => exact e2
  | cons evRhs hm _ ih => exact .cons evRhs hm (ih e2)

theorem EvalLetsN.split_append {w : World F} {d : Nat}
    {loc0 loc2 : Environment F Nat} {b1 b2 : LetBinds} {h0 h2 : Heap F}
    (ev : EvalLetsN w d loc0 (b1 ++ b2) h0 loc2 h2) :
    ∃ loc1 h1, EvalLetsN w d loc0 b1 h0 loc1 h1 ∧ EvalLetsN w d loc1 b2 h1 loc2 h2 := by
  induction b1 generalizing loc0 h0 with
  | nil => exact ⟨loc0, h0, .nil, ev⟩
  | cons hd tl ih =>
    cases ev with
    | cons evRhs hm evRest =>
      obtain ⟨loc1, h1, e1, e2⟩ := ih evRest
      exact ⟨loc1, h1, .cons evRhs hm e1, e2⟩

theorem EvalLetsN.preserves_notPEGe {w : World F} {d lo hi : Nat}
    {loc0 loc1 : Environment F Nat} {binds : LetBinds} {h0 h1 : Heap F}
    (hrange : BindsInRange lo hi binds)
    (ev : EvalLetsN w d loc0 binds h0 loc1 h1) :
    ∀ y, NotPEGe lo y → loc1.find? (·.1 == y) = loc0.find? (·.1 == y) := by
  induction ev with
  | nil => intro _ _; rfl
  | cons _ hm _ ih =>
    intro y hy
    have hp := hrange _ List.mem_cons_self
    have hrest : BindsInRange lo hi _ := fun b hb => hrange b (List.mem_cons_of_mem _ hb)
    rw [ih hrest y hy]
    exact find?_append_skip_of_binds_inRange (matchPattern_binds_inRange_aux hp hm) hy

theorem evalExprN_wrapLets_inv {w : World F} {d : Nat}
    {loc0 : Environment F Nat} {binds : LetBinds} {tail : Expr}
    {h0 h2 : Heap F} {r : SourceValue F}
    (ev : EvalExprN w d [] loc0 (qualifyExprF F (wrapLets binds tail)) h0 r h2) :
    ∃ loc1 h1,
      EvalLetsN w d loc0 binds h0 loc1 h1 ∧
      EvalExprN w d [] loc1 (qualifyExprF F tail) h1 r h2 := by
  induction binds generalizing loc0 h0 with
  | nil => exact ⟨loc0, h0, .nil, ev⟩
  | cons hd tl ih =>
    rcases hd with ⟨p, rhs⟩
    simp only [wrapLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with
    | letValue evRhs hm evBody =>
      obtain ⟨loc1, h1, evL, evT⟩ := ih evBody
      exact ⟨loc1, h1, .cons evRhs hm evL, evT⟩

theorem evalExprN_wrapLetsTail_inv {w : World F} {d : Nat}
    {loc0 : Environment F Nat} {binds : LetBinds} {tail : Expr}
    {h0 h2 : Heap F} {r : SourceValue F}
    (ev : EvalExprN w d [] loc0 (qualifyExprF F (wrapLetsTail binds tail)) h0 r h2) :
    ∃ loc1 h1,
      EvalLetsN w d loc0 binds h0 loc1 h1 ∧
      EvalExprN w d [] loc1 (qualifyExprF F tail) h1 r h2 := by
  unfold wrapLetsTail at ev
  cases hrev : binds.reverse with
  | nil =>
    rw [hrev] at ev; dsimp only at ev
    exact evalExprN_wrapLets_inv ev
  | cons hd revRest =>
    rcases hd with ⟨p, rhs⟩
    rw [hrev] at ev
    cases p with
    | bind y =>
      cases tail with
      | var z =>
        dsimp only at ev
        by_cases hyz : (y == z) = true
        · simp only [hyz, ↓reduceIte] at ev
          have heq : y = z := beq_iff_eq.mp hyz
          subst heq
          have hbinds : binds = revRest.reverse ++ [(.bind y, rhs)] := by
            have := congrArg List.reverse hrev
            simpa using this
          rw [hbinds]
          obtain ⟨locM, hM, evPrefix, evRhs⟩ := evalExprN_wrapLets_inv ev
          refine ⟨(y, r) :: locM, h2, evPrefix.append (.cons (bs := [(y, r)]) evRhs ?_ .nil), ?_⟩
          · simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]
          · simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
            exact .var (by simp [List.find?])
        · simp only [hyz, Bool.false_eq_true, ↓reduceIte] at ev
          exact evalExprN_wrapLets_inv ev
      | _ => exact evalExprN_wrapLets_inv ev
    | _ => exact evalExprN_wrapLets_inv ev

end SValOps

/-! ## Section 5: Constructive 56-bit Arithmetic Helper Contracts (`Arith56WorldSpec`) -/

section Arith56Helpers

variable {F : Type} [Field F] [DecidableEq F]

/-- Demand-guarded constructive specification of the 9 pure helpers folded by
`PartialEval.tryFoldHelperCall`. Each clause is guarded by `(∃ f ∈ fns, callsAny [nm] f.body = true)`,
so demand-linked worlds satisfy unused helper clauses vacuously. -/
structure Arith56WorldSpec (fns : List Fn) (w : World F) : Prop where
  check_u8 :
    (∃ f ∈ fns, callsAny ["check_u8"] f.body = true) →
    ∀ (k : Nat) (h : Heap F), k < 256 →
      EvalFn w (qualifyName "check_u8") [.field (k : F)] h (.tuple []) h
  check_u16 :
    (∃ f ∈ fns, callsAny ["check_u16"] f.body = true) →
    ∀ (k : Nat) (h : Heap F), k < 65536 →
      EvalFn w (qualifyName "check_u16") [.field (k : F)] h (.tuple []) h
  check_u24 :
    (∃ f ∈ fns, callsAny ["check_u24"] f.body = true) →
    ∀ (k : Nat) (h : Heap F), k < 16777216 →
      EvalFn w (qualifyName "check_u24") [.field (k : F)] h (.tuple []) h
  check_u56 :
    (∃ f ∈ fns, callsAny ["check_u56"] f.body = true) →
    ∀ (k : Nat) (h : Heap F), k < natLimit →
      EvalFn w (qualifyName "check_u56") [.field (k : F)] h (.tuple []) h
  sub_borrow_56 :
    (∃ f ∈ fns, callsAny ["sub_borrow_56"] f.body = true) →
    ∀ (a b : Nat) (h : Heap F), a < natLimit → b < natLimit →
      EvalFn w (qualifyName "sub_borrow_56") [.field (a : F), .field (b : F)] h
        (.tuple [.field ((a - b : Nat) : F), .field ((if b ≤ a then 1 else 0 : Nat) : F)]) h
  split_32_24 :
    (∃ f ∈ fns, callsAny ["split_32_24"] f.body = true) →
    ∀ (k : Nat) (h : Heap F), k < natLimit →
      EvalFn w (qualifyName "split_32_24") [.field (k : F)] h
        (.tuple [.field ((k % 4294967296 : Nat) : F), .field ((k / 4294967296 : Nat) : F)]) h
  mul_56 :
    (∃ f ∈ fns, callsAny ["mul_56"] f.body = true) →
    ∀ (a b : Nat) (h : Heap F), a < natLimit → b < natLimit → a * b < natLimit →
      EvalFn w (qualifyName "mul_56") [.field (a : F), .field (b : F)] h
        (.field ((a * b : Nat) : F)) h
  divmod_56 :
    (∃ f ∈ fns, callsAny ["divmod_56"] f.body = true) →
    ∀ (a b : Nat) (h : Heap F), a < natLimit → 0 < b → b < natLimit →
      EvalFn w (qualifyName "divmod_56") [.field (a : F), .field (b : F)] h
        (.tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)]) h
  fields_is_zero :
    (∃ f ∈ fns, callsAny ["Fields::is_zero"] f.body = true) →
    ∀ (k : Nat) (h : Heap F), k < natLimit →
      EvalFn w (qualifyName "Fields::is_zero") [.field (k : F)] h
        (.field ((if k == 0 then 1 else 0 : Nat) : F)) h

/-- Soundness of `PartialEval.tryFoldHelperCall`: whenever a helper call folds statically
to `svRes`, the original world evaluates the call on `vsOrig` without modifying the heap
to a value denoted by `svRes`. -/
theorem tryFoldHelperCall_sound {fns : List Fn} {wOrig : World F}
    (hspec : Arith56WorldSpec fns wOrig)
    {hOpt hOrig : Heap F} {locOpt : Environment F Nat}
    {nm : String} {svArgs : List SVal} {vsOrig : List (SourceValue F)} {svRes : SVal}
    (hcalled : ∃ f ∈ fns, callsAny [nm] f.body = true)
    (hargs : SValListDenotes hOpt hOrig locOpt svArgs vsOrig)
    (hfold : tryFoldHelperCall nm svArgs = some svRes) :
    ∃ vRes,
      EvalFn wOrig (qualifyName nm) vsOrig hOrig vRes hOrig ∧
      SValDenotes hOpt hOrig locOpt svRes vRes := by
  unfold tryFoldHelperCall at hfold
  split at hfold
  · -- check_u8
    rename_i k
    split at hfold
    · next hk =>
      simp only [Option.some.injEq] at hfold; subst hfold
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | cons _ _ => exact False.elim hargs.2
        | nil =>
          rcases hargs.1 with ⟨_, rfl⟩
          exact ⟨.tuple [], hspec.check_u8 hcalled k hOrig hk, ⟨[], rfl, trivial⟩⟩
    · cases hfold
  · -- check_u16
    rename_i k
    split at hfold
    · next hk =>
      simp only [Option.some.injEq] at hfold; subst hfold
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | cons _ _ => exact False.elim hargs.2
        | nil =>
          rcases hargs.1 with ⟨_, rfl⟩
          exact ⟨.tuple [], hspec.check_u16 hcalled k hOrig hk, ⟨[], rfl, trivial⟩⟩
    · cases hfold
  · -- check_u24
    rename_i k
    split at hfold
    · next hk =>
      simp only [Option.some.injEq] at hfold; subst hfold
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | cons _ _ => exact False.elim hargs.2
        | nil =>
          rcases hargs.1 with ⟨_, rfl⟩
          exact ⟨.tuple [], hspec.check_u24 hcalled k hOrig hk, ⟨[], rfl, trivial⟩⟩
    · cases hfold
  · -- check_u56
    rename_i k
    split at hfold
    · next hk =>
      simp only [Option.some.injEq] at hfold; subst hfold
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | cons _ _ => exact False.elim hargs.2
        | nil =>
          rcases hargs.1 with ⟨_, rfl⟩
          exact ⟨.tuple [], hspec.check_u56 hcalled k hOrig hk, ⟨[], rfl, trivial⟩⟩
    · cases hfold
  · -- sub_borrow_56
    rename_i a b
    split at hfold
    · next hab =>
      simp only [Option.some.injEq] at hfold; subst hfold
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | nil => exact False.elim hargs.2
        | cons v2 vs2 =>
          cases vs2 with
          | cons _ _ => exact False.elim hargs.2.2
          | nil =>
            rcases hargs.1 with ⟨_, rfl⟩
            rcases hargs.2.1 with ⟨_, rfl⟩
            refine ⟨_, hspec.sub_borrow_56 hcalled a b hOrig hab.1 hab.2, ?_⟩
            refine ⟨[.field ((a - b : Nat) : F), .field ((if b ≤ a then 1 else 0 : Nat) : F)], rfl, ?_⟩
            refine ⟨⟨by omega, rfl⟩, ⟨?_, rfl⟩, trivial⟩
            split <;> unfold natLimit <;> omega
    · cases hfold
  · -- split_32_24
    rename_i k
    split at hfold
    · next hk =>
      simp only [Option.some.injEq] at hfold; subst hfold
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | cons _ _ => exact False.elim hargs.2
        | nil =>
          rcases hargs.1 with ⟨_, rfl⟩
          refine ⟨_, hspec.split_32_24 hcalled k hOrig hk, ?_⟩
          refine ⟨[.field ((k % 4294967296 : Nat) : F), .field ((k / 4294967296 : Nat) : F)], rfl, ?_⟩
          exact ⟨⟨by unfold natLimit at *; omega, rfl⟩, ⟨by unfold natLimit at *; omega, rfl⟩, trivial⟩
    · cases hfold
  · -- mul_56
    rename_i a b
    split at hfold
    · next hab =>
      simp only [Option.some.injEq] at hfold; subst hfold
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | nil => exact False.elim hargs.2
        | cons v2 vs2 =>
          cases vs2 with
          | cons _ _ => exact False.elim hargs.2.2
          | nil =>
            rcases hargs.1 with ⟨_, rfl⟩
            rcases hargs.2.1 with ⟨_, rfl⟩
            exact ⟨_, hspec.mul_56 hcalled a b hOrig hab.1.1 hab.1.2 hab.2, ⟨hab.2, rfl⟩⟩
    · cases hfold
  · -- divmod_56
    rename_i a b
    split at hfold
    · next hab =>
      simp only [Option.some.injEq] at hfold; subst hfold
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | nil => exact False.elim hargs.2
        | cons v2 vs2 =>
          cases vs2 with
          | cons _ _ => exact False.elim hargs.2.2
          | nil =>
            rcases hargs.1 with ⟨_, rfl⟩
            rcases hargs.2.1 with ⟨_, rfl⟩
            refine ⟨_, hspec.divmod_56 hcalled a b hOrig hab.1.1 hab.1.2 hab.2, ?_⟩
            refine ⟨[.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)], rfl, ?_⟩
            have hdiv : a / b < natLimit := Nat.lt_of_le_of_lt (Nat.div_le_self a b) hab.1.1
            have hmod : a % b < natLimit := Nat.lt_trans (Nat.mod_lt a hab.1.2) hab.2
            exact ⟨⟨hdiv, rfl⟩, ⟨hmod, rfl⟩, trivial⟩
    · cases hfold
  · -- Fields::is_zero
    rename_i k
    split at hfold
    · next hk =>
      simp only [Option.some.injEq] at hfold; subst hfold
      cases vsOrig with
      | nil => exact False.elim hargs
      | cons v1 vs1 =>
        cases vs1 with
        | cons _ _ => exact False.elim hargs.2
        | nil =>
          rcases hargs.1 with ⟨_, rfl⟩
          refine ⟨_, hspec.fields_is_zero hcalled k hOrig hk, ⟨?_, rfl⟩⟩
          split <;> unfold natLimit <;> omega
    · cases hfold
  · cases hfold

/-! ### Constructive Forward Derivations for `TypedLower`'s 56-bit Gadgets -/

/-- `i`-th little-endian byte of natural number `k`. -/
def byteAt (k i : Nat) : Nat := (k / 256 ^ i) % 256

theorem byteAt_lt (k i : Nat) : byteAt k i < 256 :=
  Nat.mod_lt _ (by omega)

theorem byteAt_eq_zero {k i : Nat} (h : k < 256 ^ i) : byteAt k i = 0 := by
  unfold byteAt; simp [Nat.div_eq_of_lt h]

/-- Constant 8-byte little-endian decomposition witness for `bytes_le` hints. -/
def bytes8Const (F : Type) [NatCast F] (k : Nat) : Aiur.Constant F :=
  .tuple [.field (byteAt k 0 : F), .field (byteAt k 1 : F), .field (byteAt k 2 : F),
          .field (byteAt k 3 : F), .field (byteAt k 4 : F), .field (byteAt k 5 : F),
          .field (byteAt k 6 : F), .field (byteAt k 7 : F)]

/-- Constant 2-field tuple witness for `ixcc.divmod` hints. -/
def tuple2Const (F : Type) [NatCast F] (q r : Nat) : Aiur.Constant F :=
  .tuple [.field (q : F), .field (r : F)]

/-- Constructive byte-check availability in `w` (for either the 256-row `U8Byte::check`
tier or the `UInt8::from_fields` pair tier). -/
def ByteCheckProvides (w : World F) (usePair : Bool) : Prop :=
  if usePair then
    ∀ b1 b2 : Nat, b1 < 256 → b2 < 256 → ∀ h : Heap F,
      ∃ v, EvalFn w "UInt8::from_fields" [.field (b1 : F), .field (b2 : F)] h v h
  else
    ∀ b : Nat, b < 256 → ∀ h : Heap F,
      EvalFn w "U8Byte::check" [.field (b : F)] h (.tuple []) h

/-- Typing availability for the two constant shapes emitted by `TypedLower`'s 56-bit hints
(`bytes_le` → `[Field; 8]` and `ixcc.divmod` → `(Field, Field)`). -/
structure Arith56HintsTyped (w : World F) : Prop where
  bytes8_typed : ∀ k : Nat,
    w.typed ((Aiur.Generic.Ty.array .field 8).subst []).toCore (bytes8Const F k) = true
  tuple2_typed : ∀ q r : Nat,
    w.typed ((Aiur.Generic.Ty.tuple [.field, .field]).subst []).toCore (tuple2Const F q r) = true

private theorem mk_let_wild {w : World F} {loc : Environment F Nat}
    {e body : Aiur.Generic.Expr F} {h : Heap F} {v r : SourceValue F}
    (ev1 : EvalExpr w [] loc e h v h) (ev2 : EvalExpr w [] loc body h r h) :
    EvalExpr w [] loc (.letValue .wildcard e body) h r h :=
  .letValue (bindings := []) ev1 (by simp [World.matchPattern, matchPatternWith]) ev2

private theorem mk_let_bind {w : World F} {loc : Environment F Nat} {x : String}
    {e body : Aiur.Generic.Expr F} {h : Heap F} {v r : SourceValue F}
    (ev1 : EvalExpr w [] loc e h v h)
    (ev2 : EvalExpr w [] ((x, v) :: loc) body h r h) :
    EvalExpr w [] loc (.letValue (.bind x) e body) h r h :=
  .letValue (bindings := [(x, v)]) ev1 (by simp [World.matchPattern, matchPatternWith]) ev2

private theorem mk_let_tuple2 {w : World F} {loc : Environment F Nat} {x y : String}
    {e body : Aiur.Generic.Expr F} {h : Heap F} {v1 v2 r : SourceValue F}
    (ev1 : EvalExpr w [] loc e h (.tuple [v1, v2]) h)
    (ev2 : EvalExpr w [] ((x, v1) :: (y, v2) :: loc) body h r h) :
    EvalExpr w [] loc (.letValue (.tuple [.bind x, .bind y]) e body) h r h :=
  .letValue (bindings := [(x, v1), (y, v2)]) ev1
    (by simp [World.matchPattern, matchPatternWith, matchListWith]) ev2

private theorem mk_let_tuple2_wild1 {w : World F} {loc : Environment F Nat} {y : String}
    {e body : Aiur.Generic.Expr F} {h : Heap F} {v1 v2 r : SourceValue F}
    (ev1 : EvalExpr w [] loc e h (.tuple [v1, v2]) h)
    (ev2 : EvalExpr w [] ((y, v2) :: loc) body h r h) :
    EvalExpr w [] loc (.letValue (.tuple [.wildcard, .bind y]) e body) h r h :=
  .letValue (bindings := [(y, v2)]) ev1
    (by simp [World.matchPattern, matchPatternWith, matchListWith]) ev2

private theorem mk_assertEq_field {w : World F} {loc : Environment F Nat}
    {msg : Aiur.Assertion} {a b : Aiur.Generic.Expr F} {h : Heap F} {x y : F}
    (eva : EvalExpr w [] loc a h (.field x) h) (evb : EvalExpr w [] loc b h (.field y) h)
    (hxy : x = y) :
    EvalExpr w [] loc (.builtin (.assertEq msg) [a, b]) h (.tuple []) h := by
  subst hxy
  exact .builtin (.cons eva (.cons evb .nil))
    (by simp [Builtin.apply, evalAssertEq, Value.pointerFree])

private theorem mk_add {w : World F} {loc : Environment F Nat}
    {a b : Aiur.Generic.Expr F} {h : Heap F} {x y : F}
    (eva : EvalExpr w [] loc a h (.field x) h) (evb : EvalExpr w [] loc b h (.field y) h) :
    EvalExpr w [] loc (.binary .add a b) h (.field (x + y)) h :=
  .binary eva evb (by simp [evalBinOp])

private theorem mk_sub {w : World F} {loc : Environment F Nat}
    {a b : Aiur.Generic.Expr F} {h : Heap F} {x y : F}
    (eva : EvalExpr w [] loc a h (.field x) h) (evb : EvalExpr w [] loc b h (.field y) h) :
    EvalExpr w [] loc (.binary .sub a b) h (.field (x - y)) h :=
  .binary eva evb (by simp [evalBinOp])

private theorem mk_mul {w : World F} {loc : Environment F Nat}
    {a b : Aiur.Generic.Expr F} {h : Heap F} {x y : F}
    (eva : EvalExpr w [] loc a h (.field x) h) (evb : EvalExpr w [] loc b h (.field y) h) :
    EvalExpr w [] loc (.binary .mul a b) h (.field (x * y)) h :=
  .binary eva evb (by simp [evalBinOp])

private def bytes8Env (F : Type) [NatCast F] (k : Nat) : Environment F Nat :=
  [("b0", .field (byteAt k 0 : F)), ("b1", .field (byteAt k 1 : F)),
   ("b2", .field (byteAt k 2 : F)), ("b3", .field (byteAt k 3 : F)),
   ("b4", .field (byteAt k 4 : F)), ("b5", .field (byteAt k 5 : F)),
   ("b6", .field (byteAt k 6 : F)), ("b7", .field (byteAt k 7 : F))]

omit [DecidableEq F] in
private theorem bytes8Const_toValue (k : Nat) :
    ((bytes8Const F k).toValue : SourceValue F) =
      .tuple [.field (byteAt k 0 : F), .field (byteAt k 1 : F), .field (byteAt k 2 : F),
              .field (byteAt k 3 : F), .field (byteAt k 4 : F), .field (byteAt k 5 : F),
              .field (byteAt k 6 : F), .field (byteAt k 7 : F)] := by
  simp [bytes8Const, Aiur.Constant.toValue, Aiur.Value.mapAddress]

omit [DecidableEq F] in
private theorem tuple2Const_toValue (q r : Nat) :
    ((tuple2Const F q r).toValue : SourceValue F) =
      .tuple [.field (q : F), .field (r : F)] := by
  simp [tuple2Const, Aiur.Constant.toValue, Aiur.Value.mapAddress]

private theorem mk_let_bytes8 {w : World F} {loc : Environment F Nat}
    {kExpr body : Aiur.Generic.Expr F} {h : Heap F} {kv r : SourceValue F} {n : Nat}
    (ht : w.typed ((Aiur.Generic.Ty.array .field 8).subst []).toCore (bytes8Const F n) = true)
    (evk : EvalExpr w [] loc kExpr h kv h)
    (evBody : EvalExpr w [] (bytes8Env F n ++ loc) body h r h) :
    EvalExpr w [] loc
      (.letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                          .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) kExpr "bytes_le") body) h r h := by
  refine .letValue (bindings := bytes8Env F n) (.hint evk ht) ?_ evBody
  rw [bytes8Const_toValue]
  simp [World.matchPattern, matchPatternWith, matchListWith, bytes8Env]

private theorem mk_check_b_false {w : World F} (hbc : ByteCheckProvides w false)
    {k : Nat} {loc : Environment F Nat} {h : Heap F} {v : SourceValue F}
    {nm : String} {i : Nat}
    (hl : loc.find? (·.1 == nm) = some (nm, .field (byteAt k i : F)))
    {body : Aiur.Generic.Expr F} (evb : EvalExpr w [] loc body h v h) :
    EvalExpr w [] loc (.letValue .wildcard (.call "U8Byte::check" (some []) [.var nm]) body) h v h :=
  mk_let_wild (.call (.cons (.var hl) .nil) (hbc (byteAt k i) (byteAt_lt k i) h)) evb

private theorem mk_check_pair_true {w : World F} (hbc : ByteCheckProvides w true)
    {k : Nat} {loc : Environment F Nat} {h : Heap F} {v : SourceValue F}
    {nm1 nm2 : String} {i j : Nat}
    (hl1 : loc.find? (·.1 == nm1) = some (nm1, .field (byteAt k i : F)))
    (hl2 : loc.find? (·.1 == nm2) = some (nm2, .field (byteAt k j : F)))
    {body : Aiur.Generic.Expr F} (evb : EvalExpr w [] loc body h v h) :
    EvalExpr w [] loc
      (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var nm1, .var nm2]) body) h v h := by
  obtain ⟨u, hfn⟩ := hbc (byteAt k i) (byteAt k j) (byteAt_lt k i) (byteAt_lt k j) h
  exact mk_let_wild (.call (.cons (.var hl1) (.cons (.var hl2) .nil)) hfn) evb

private theorem mk_check_single_true {w : World F} (hbc : ByteCheckProvides w true)
    {k : Nat} {loc : Environment F Nat} {h : Heap F} {v : SourceValue F}
    {nm : String} {i : Nat}
    (hl : loc.find? (·.1 == nm) = some (nm, .field (byteAt k i : F)))
    {body : Aiur.Generic.Expr F} (evb : EvalExpr w [] loc body h v h) :
    EvalExpr w [] loc
      (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var nm, .literal (0 : F)]) body) h v h := by
  obtain ⟨u, hfn⟩ := hbc (byteAt k i) 0 (byteAt_lt k i) (by omega) h
  have hfn' : EvalFn w "UInt8::from_fields" [.field (byteAt k i : F), .field (0 : F)] h u h := by
    simpa using hfn
  exact mk_let_wild (.call (.cons (.var hl) (.cons .literal .nil)) hfn') evb

/-- Constructive forward derivation of `Prog::check_u8(k)` for `k < 256`. -/
theorem evalFn_check_u8_mk {w : World F} {usePair : Bool}
    (hbc : ByteCheckProvides w usePair)
    (hprov : WorldProvidesFn w (qualified "check_u8") ["x"] (qualifyExprF F (checkU8Fn usePair).body))
    (k : Nat) (h : Heap F) (hk : k < 256) :
    EvalFn w (qualified "check_u8") [.field (k : F)] h (.tuple []) h := by
  apply EvalFn.intro (hprov [.field (k : F)] rfl)
  simp only [List.zip, List.zipWith]
  cases usePair with
  | false =>
    rw [show (checkU8Fn false).body = .call "U8Byte::check" (some []) [.var "x"] from rfl]
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, Option.map_some, List.map,
      TypedGadgets.qualifyName_u8Byte_check]
    exact .call (.cons (.var (by simp)) .nil) (hbc k hk h)
  | true =>
    rw [show (checkU8Fn true).body =
      .letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "x", .literal 0]) (.tuple []) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
      Option.map_some, List.map, Nat.cast_zero, TypedGadgets.qualifyName_u8_from_fields]
    obtain ⟨u, hfn⟩ := hbc k 0 hk (by omega) h
    have hfn' : EvalFn w "UInt8::from_fields" [.field (k : F), .field (0 : F)] h u h := by
      simpa using hfn
    exact mk_let_wild (.call (.cons (.var (by simp)) (.cons .literal .nil)) hfn') (.tuple .nil)

/-- Constructive forward derivation of `Prog::check_u16(k)` for `k < 2^16`. -/
theorem evalFn_check_u16_mk {w : World F} {usePair : Bool}
    (hbc : ByteCheckProvides w usePair) (hhints : Arith56HintsTyped w)
    (hprov : WorldProvidesFn w (qualified "check_u16") ["x"] (qualifyExprF F (checkU16Fn usePair).body))
    (k : Nat) (h : Heap F) (hk : k < 65536) :
    EvalFn w (qualified "check_u16") [.field (k : F)] h (.tuple []) h := by
  apply EvalFn.intro (hprov [.field (k : F)] rfl)
  simp only [List.zip, List.zipWith]
  have hb2 : byteAt k 2 = 0 := byteAt_eq_zero (by omega)
  have hb3 : byteAt k 3 = 0 := byteAt_eq_zero (by omega)
  have hb4 : byteAt k 4 = 0 := byteAt_eq_zero (by omega)
  have hb5 : byteAt k 5 = 0 := byteAt_eq_zero (by omega)
  have hb6 : byteAt k 6 = 0 := byteAt_eq_zero (by omega)
  have hb7 : byteAt k 7 = 0 := byteAt_eq_zero (by omega)
  have hrec : (byteAt k 0 : F) + ((256 : Nat) : F) * (byteAt k 1 : F) = (k : F) := by
    have hnat : byteAt k 0 + 256 * byteAt k 1 = k := by unfold byteAt; omega
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have htail :
      EvalExpr w [] (bytes8Env F k ++ [("x", .field (k : F))])
        (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b2", .literal (0 : F)])
          (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b3", .literal (0 : F)])
            (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b4", .literal (0 : F)])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b5", .literal (0 : F)])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b6", .literal (0 : F)])
                  (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b7", .literal (0 : F)])
                    (.letValue .wildcard
                      (.builtin (.assertEq (Lower.assertion "u16: bytes do not recompose"))
                        [.binary .add (.var "b0") (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1")), .var "x"])
                      (.tuple [])))))))) h (.tuple []) h := by
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb2])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb3])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb4])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb5])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb6])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb7])) ?_
    refine mk_let_wild (mk_assertEq_field
      (mk_add (.var (by simp [bytes8Env])) (mk_mul (.literal (value := ((256 : Nat) : F))) (.var (by simp [bytes8Env]))))
      (.var (by simp [bytes8Env])) hrec) (.tuple .nil)
  cases usePair with
  | false =>
    rw [show (checkU16Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b2", .literal 0])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b3", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b4", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b5", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b6", .literal 0])
                      (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b7", .literal 0])
                        (.letValue .wildcard
                          (.builtin (.assertEq (Lower.assertion "u16: bytes do not recompose"))
                            [.binary .add (.var "b0") (.binary .mul (.literal 256) (.var "b1")), .var "x"])
                          (.tuple [])))))))))) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8Byte_check]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    refine mk_check_b_false hbc (k := k) (i := 0) (by simp [bytes8Env]) ?_
    refine mk_check_b_false hbc (k := k) (i := 1) (by simp [bytes8Env]) htail
  | true =>
    rw [show (checkU16Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b2", .literal 0])
            (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b3", .literal 0])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b4", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b5", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b6", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u16: high bytes must be zero")) [.var "b7", .literal 0])
                      (.letValue .wildcard
                        (.builtin (.assertEq (Lower.assertion "u16: bytes do not recompose"))
                          [.binary .add (.var "b0") (.binary .mul (.literal 256) (.var "b1")), .var "x"])
                        (.tuple []))))))))) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8_from_fields]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    exact mk_check_pair_true hbc (k := k) (i := 0) (j := 1) (by simp [bytes8Env]) (by simp [bytes8Env]) htail

/-- Constructive forward derivation of `Prog::check_u24(k)` for `k < 2^24`. -/
theorem evalFn_check_u24_mk {w : World F} {usePair : Bool}
    (hbc : ByteCheckProvides w usePair) (hhints : Arith56HintsTyped w)
    (hprov : WorldProvidesFn w (qualified "check_u24") ["x"] (qualifyExprF F (checkU24Fn usePair).body))
    (k : Nat) (h : Heap F) (hk : k < 16777216) :
    EvalFn w (qualified "check_u24") [.field (k : F)] h (.tuple []) h := by
  apply EvalFn.intro (hprov [.field (k : F)] rfl)
  simp only [List.zip, List.zipWith]
  have hb3 : byteAt k 3 = 0 := byteAt_eq_zero (by omega)
  have hb4 : byteAt k 4 = 0 := byteAt_eq_zero (by omega)
  have hb5 : byteAt k 5 = 0 := byteAt_eq_zero (by omega)
  have hb6 : byteAt k 6 = 0 := byteAt_eq_zero (by omega)
  have hb7 : byteAt k 7 = 0 := byteAt_eq_zero (by omega)
  have hrec : (byteAt k 0 : F) + (((256 : Nat) : F) * (byteAt k 1 : F) + ((65536 : Nat) : F) * (byteAt k 2 : F)) = (k : F) := by
    have hnat : byteAt k 0 + (256 * byteAt k 1 + 65536 * byteAt k 2) = k := by unfold byteAt; omega
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have htail :
      EvalExpr w [] (bytes8Env F k ++ [("x", .field (k : F))])
        (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b3", .literal (0 : F)])
          (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b4", .literal (0 : F)])
            (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b5", .literal (0 : F)])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b6", .literal (0 : F)])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b7", .literal (0 : F)])
                  (.letValue .wildcard
                    (.builtin (.assertEq (Lower.assertion "u24: bytes do not recompose"))
                      [.binary .add (.var "b0")
                        (.binary .add (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1"))
                          (.binary .mul (.literal ((65536 : Nat) : F)) (.var "b2"))), .var "x"])
                    (.tuple []))))))) h (.tuple []) h := by
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb3])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb4])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb5])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb6])) ?_
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb7])) ?_
    refine mk_let_wild (mk_assertEq_field
      (mk_add (.var (by simp [bytes8Env]))
        (mk_add (mk_mul (.literal (value := ((256 : Nat) : F))) (.var (by simp [bytes8Env])))
          (mk_mul (.literal (value := ((65536 : Nat) : F))) (.var (by simp [bytes8Env])))))
      (.var (by simp [bytes8Env])) hrec) (.tuple .nil)
  cases usePair with
  | false =>
    rw [show (checkU24Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b3", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b4", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b5", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b6", .literal 0])
                      (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b7", .literal 0])
                        (.letValue .wildcard
                          (.builtin (.assertEq (Lower.assertion "u24: bytes do not recompose"))
                            [.binary .add (.var "b0")
                              (.binary .add (.binary .mul (.literal 256) (.var "b1"))
                                (.binary .mul (.literal 65536) (.var "b2"))), .var "x"])
                          (.tuple [])))))))))) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8Byte_check]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    refine mk_check_b_false hbc (k := k) (i := 0) (by simp [bytes8Env]) ?_
    refine mk_check_b_false hbc (k := k) (i := 1) (by simp [bytes8Env]) ?_
    refine mk_check_b_false hbc (k := k) (i := 2) (by simp [bytes8Env]) htail
  | true =>
    rw [show (checkU24Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .literal 0])
            (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b3", .literal 0])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b4", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b5", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b6", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u24: high bytes must be zero")) [.var "b7", .literal 0])
                      (.letValue .wildcard
                        (.builtin (.assertEq (Lower.assertion "u24: bytes do not recompose"))
                          [.binary .add (.var "b0")
                            (.binary .add (.binary .mul (.literal 256) (.var "b1"))
                              (.binary .mul (.literal 65536) (.var "b2"))), .var "x"])
                        (.tuple []))))))))) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8_from_fields]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    refine mk_check_pair_true hbc (k := k) (i := 0) (j := 1) (by simp [bytes8Env]) (by simp [bytes8Env]) ?_
    exact mk_check_single_true hbc (k := k) (i := 2) (by simp [bytes8Env]) htail

/-- Shared helper: 7-byte range check sequence on `b0..b6` inside `bytes8Env F k ++ loc`. -/
private theorem mk_check_7bytes_false {w : World F} (hbc : ByteCheckProvides w false)
    {k : Nat} {loc : Environment F Nat} {h : Heap F} {v : SourceValue F}
    {tail : Aiur.Generic.Expr F}
    (evTail : EvalExpr w [] (bytes8Env F k ++ loc) tail h v h) :
    EvalExpr w [] (bytes8Env F k ++ loc)
      (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                    tail))))))) h v h := by
  refine mk_check_b_false hbc (k := k) (i := 0) (by simp [bytes8Env]) ?_
  refine mk_check_b_false hbc (k := k) (i := 1) (by simp [bytes8Env]) ?_
  refine mk_check_b_false hbc (k := k) (i := 2) (by simp [bytes8Env]) ?_
  refine mk_check_b_false hbc (k := k) (i := 3) (by simp [bytes8Env]) ?_
  refine mk_check_b_false hbc (k := k) (i := 4) (by simp [bytes8Env]) ?_
  refine mk_check_b_false hbc (k := k) (i := 5) (by simp [bytes8Env]) ?_
  exact mk_check_b_false hbc (k := k) (i := 6) (by simp [bytes8Env]) evTail

private theorem mk_check_7bytes_true {w : World F} (hbc : ByteCheckProvides w true)
    {k : Nat} {loc : Environment F Nat} {h : Heap F} {v : SourceValue F}
    {tail : Aiur.Generic.Expr F}
    (evTail : EvalExpr w [] (bytes8Env F k ++ loc) tail h v h) :
    EvalExpr w [] (bytes8Env F k ++ loc)
      (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal (0 : F)])
              tail)))) h v h := by
  refine mk_check_pair_true hbc (k := k) (i := 0) (j := 1) (by simp [bytes8Env]) (by simp [bytes8Env]) ?_
  refine mk_check_pair_true hbc (k := k) (i := 2) (j := 3) (by simp [bytes8Env]) (by simp [bytes8Env]) ?_
  refine mk_check_pair_true hbc (k := k) (i := 4) (j := 5) (by simp [bytes8Env]) (by simp [bytes8Env]) ?_
  exact mk_check_single_true hbc (k := k) (i := 6) (by simp [bytes8Env]) evTail

private def recompose7ExprF (F : Type) [NatCast F] : Aiur.Generic.Expr F :=
  .binary .add (.var "b0")
    (.binary .add (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1"))
      (.binary .add (.binary .mul (.literal ((65536 : Nat) : F)) (.var "b2"))
        (.binary .add (.binary .mul (.literal ((16777216 : Nat) : F)) (.var "b3"))
          (.binary .add (.binary .mul (.literal ((4294967296 : Nat) : F)) (.var "b4"))
            (.binary .add (.binary .mul (.literal ((1099511627776 : Nat) : F)) (.var "b5"))
              (.binary .mul (.literal ((281474976710656 : Nat) : F)) (.var "b6")))))))

private theorem eval_recompose7ExprF {w : World F} {k : Nat} {loc : Environment F Nat} {h : Heap F} :
    EvalExpr w [] (bytes8Env F k ++ loc) (recompose7ExprF F) h (.field ((k % natLimit : Nat) : F)) h := by
  have hnat :
      byteAt k 0 + (256 * byteAt k 1 + (65536 * byteAt k 2 + (16777216 * byteAt k 3 +
        (4294967296 * byteAt k 4 + (1099511627776 * byteAt k 5 + 281474976710656 * byteAt k 6))))) =
      k % natLimit := by
    unfold byteAt natLimit; omega
  have hF :
      (byteAt k 0 : F) + (((256 : Nat) : F) * (byteAt k 1 : F) +
        (((65536 : Nat) : F) * (byteAt k 2 : F) +
          (((16777216 : Nat) : F) * (byteAt k 3 : F) +
            (((4294967296 : Nat) : F) * (byteAt k 4 : F) +
              (((1099511627776 : Nat) : F) * (byteAt k 5 : F) +
                ((281474976710656 : Nat) : F) * (byteAt k 6 : F)))))) =
      ((k % natLimit : Nat) : F) := by
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  rw [← hF]
  unfold recompose7ExprF
  exact mk_add (.var (by simp [bytes8Env]))
    (mk_add (mk_mul .literal (.var (by simp [bytes8Env])))
      (mk_add (mk_mul .literal (.var (by simp [bytes8Env])))
        (mk_add (mk_mul .literal (.var (by simp [bytes8Env])))
          (mk_add (mk_mul .literal (.var (by simp [bytes8Env])))
            (mk_add (mk_mul .literal (.var (by simp [bytes8Env])))
              (mk_mul .literal (.var (by simp [bytes8Env]))))))))

private def recompose7ExprNat : Expr :=
  .binary .add (.var "b0")
    (.binary .add (.binary .mul (.literal 256) (.var "b1"))
      (.binary .add (.binary .mul (.literal 65536) (.var "b2"))
        (.binary .add (.binary .mul (.literal 16777216) (.var "b3"))
          (.binary .add (.binary .mul (.literal 4294967296) (.var "b4"))
            (.binary .add (.binary .mul (.literal 1099511627776) (.var "b5"))
              (.binary .mul (.literal 281474976710656) (.var "b6")))))))

/-- Constructive forward derivation of `Prog::check_u56(k)` for `k < 2^56`. -/
theorem evalFn_check_u56_mk {w : World F} {usePair : Bool}
    (hbc : ByteCheckProvides w usePair) (hhints : Arith56HintsTyped w)
    (hprov : WorldProvidesFn w (qualified "check_u56") ["x"] (qualifyExprF F (checkU56Fn usePair).body))
    (k : Nat) (h : Heap F) (hk : k < natLimit) :
    EvalFn w (qualified "check_u56") [.field (k : F)] h (.tuple []) h := by
  apply EvalFn.intro (hprov [.field (k : F)] rfl)
  simp only [List.zip, List.zipWith]
  have hb7 : byteAt k 7 = 0 := byteAt_eq_zero (by unfold natLimit at hk; omega)
  have hmod : k % natLimit = k := Nat.mod_eq_of_lt hk
  have htail :
      EvalExpr w [] (bytes8Env F k ++ [("x", .field (k : F))])
        (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u56: top byte must be zero")) [.var "b7", .literal (0 : F)])
          (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u56: bytes do not recompose"))
            [recompose7ExprF F, .var "x"]) (.tuple []))) h (.tuple []) h := by
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb7])) ?_
    refine mk_let_wild (mk_assertEq_field eval_recompose7ExprF (.var (by simp [bytes8Env]; rfl)) (by simp [hmod]))
      (.tuple .nil)
  cases usePair with
  | false =>
    rw [show (checkU56Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                    (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                      (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u56: top byte must be zero")) [.var "b7", .literal 0])
                        (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u56: bytes do not recompose"))
                          [recompose7ExprNat, .var "x"]) (.tuple [])))))))))) from rfl]
    simp only [recompose7ExprNat, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8Byte_check]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    exact mk_check_7bytes_false hbc htail
  | true =>
    rw [show (checkU56Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
              (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u56: top byte must be zero")) [.var "b7", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "u56: bytes do not recompose"))
                    [recompose7ExprNat, .var "x"]) (.tuple []))))))) from rfl]
    simp only [recompose7ExprNat, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8_from_fields]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    exact mk_check_7bytes_true hbc htail

/-- Constructive forward derivation of `Prog::sub_borrow_56(a, b)` for `a, b < 2^56`. -/
theorem evalFn_sub_borrow_56_mk {w : World F} {usePair : Bool}
    (hbc : ByteCheckProvides w usePair) (hhints : Arith56HintsTyped w)
    (hprov : WorldProvidesFn w (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (a b : Nat) (h : Heap F) (ha : a < natLimit) (hb : b < natLimit) :
    EvalFn w (qualified "sub_borrow_56") [.field (a : F), .field (b : F)] h
      (.tuple [.field ((a - b : Nat) : F), .field ((if b ≤ a then 1 else 0 : Nat) : F)]) h := by
  apply EvalFn.intro (hprov [.field (a : F), .field (b : F)] rfl)
  simp only [List.zip, List.zipWith]
  let zNat : Nat := a + natLimit - b
  have hzF : (a : F) - (b : F) + (natLimit : F) = (zNat : F) := by
    have hle : b ≤ a + natLimit := by omega
    have hadd : zNat + b = a + natLimit := Nat.sub_add_cancel hle
    have hcast : (zNat : F) + (b : F) = (a : F) + (natLimit : F) := by
      have := congrArg (Nat.cast : Nat → F) hadd
      simpa [Nat.cast_add] using this
    calc (a : F) - (b : F) + (natLimit : F)
        = (a : F) + (natLimit : F) - (b : F) := by ring
      _ = ((zNat : F) + (b : F)) - (b : F) := by rw [← hcast]
      _ = (zNat : F) := by ring
  have hb7_eq : byteAt zNat 7 = if b ≤ a then 1 else 0 := by
    dsimp only [zNat, byteAt]
    unfold natLimit at *
    split <;> omega
  have hb7_bool : (byteAt zNat 7 : F) * ((byteAt zNat 7 : F) - (1 : F)) = (0 : F) := by
    rw [hb7_eq]; split <;> simp
  have hrecomp :
      ((zNat % natLimit : Nat) : F) + (natLimit : F) * (byteAt zNat 7 : F) = (zNat : F) := by
    have hnat : zNat % natLimit + natLimit * byteAt zNat 7 = zNat := by
      dsimp only [zNat, byteAt]
      unfold natLimit at *
      omega
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have hres0 : (byteAt zNat 7 : F) * ((zNat % natLimit : Nat) : F) = ((a - b : Nat) : F) := by
    rw [hb7_eq]
    by_cases hba : b ≤ a
    · simp only [hba, ↓reduceIte, Nat.cast_one, one_mul]
      have hmod : zNat % natLimit = a - b := by
        dsimp only [zNat]; unfold natLimit at *; omega
      rw [hmod]
    · simp only [hba, ↓reduceIte, Nat.cast_zero, zero_mul]
      have hsub : a - b = 0 := by omega
      simp [hsub]
  let env0 : Environment F Nat := [("x", .field (a : F)), ("y", .field (b : F))]
  let envZ : Environment F Nat := ("z", .field (zNat : F)) :: env0
  have evZ : EvalExpr w [] env0
      (.binary .add (.binary .sub (.var "x") (.var "y")) (.literal (natLimit : F)))
      h (.field (zNat : F)) h := by
    rw [← hzF]
    exact mk_add (mk_sub (.var (by simp [env0])) (.var (by simp [env0]))) .literal
  have htail :
      EvalExpr w [] (bytes8Env F zNat ++ envZ)
        (.letValue .wildcard
          (.builtin (.assertEq (Lower.assertion "sub_borrow_56: b7 not boolean"))
            [.binary .mul (.var "b7") (.binary .sub (.var "b7") (.literal (1 : F))), .literal (0 : F)])
          (.letValue (.bind "lo") (recompose7ExprF F)
            (.letValue .wildcard
              (.builtin (.assertEq (Lower.assertion "sub_borrow_56: recomposition failed"))
                [.binary .add (.var "lo") (.binary .mul (.literal (natLimit : F)) (.var "b7")), .var "z"])
              (.tuple [.binary .mul (.var "b7") (.var "lo"), .var "b7"]))))
        h (.tuple [.field ((a - b : Nat) : F), .field ((if b ≤ a then 1 else 0 : Nat) : F)]) h := by
    refine mk_let_wild
      (mk_assertEq_field
        (mk_mul (.var (by simp [bytes8Env])) (mk_sub (.var (by simp [bytes8Env])) (.literal (value := (1 : F)))))
        (.literal (value := (0 : F))) hb7_bool) ?_
    refine mk_let_bind eval_recompose7ExprF ?_
    refine mk_let_wild
      (mk_assertEq_field
        (mk_add (.var (by simp)) (mk_mul (.literal (value := (natLimit : F))) (.var (by simp [bytes8Env]))))
        (.var (by simp [bytes8Env, envZ])) hrecomp) ?_
    have ev0 : EvalExpr w [] (("lo", .field ((zNat % natLimit : Nat) : F)) :: (bytes8Env F zNat ++ envZ))
        (.binary .mul (.var "b7") (.var "lo")) h (.field ((a - b : Nat) : F)) h := by
      rw [← hres0]
      exact mk_mul (.var (by simp [bytes8Env])) (.var (by simp))
    have ev1 : EvalExpr w [] (("lo", .field ((zNat % natLimit : Nat) : F)) :: (bytes8Env F zNat ++ envZ))
        (.var "b7") h (.field ((if b ≤ a then 1 else 0 : Nat) : F)) h := by
      rw [← hb7_eq]
      exact .var (by simp [bytes8Env])
    exact .tuple (.cons ev0 (.cons ev1 .nil))
  cases usePair with
  | false =>
    rw [show (subBorrow56Fn false).body =
      .letValue (.bind "z") (.binary .add (.binary .sub (.var "x") (.var "y")) (.literal natLimit))
        (.letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                            .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
          (.hint (.array .field 8) (.var "z") "bytes_le")
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                    (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                      (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                        (.letValue .wildcard
                          (.builtin (.assertEq (Lower.assertion "sub_borrow_56: b7 not boolean"))
                            [.binary .mul (.var "b7") (.binary .sub (.var "b7") (.literal 1)), .literal 0])
                          (.letValue (.bind "lo") recompose7ExprNat
                            (.letValue .wildcard
                              (.builtin (.assertEq (Lower.assertion "sub_borrow_56: recomposition failed"))
                                [.binary .add (.var "lo") (.binary .mul (.literal natLimit) (.var "b7")), .var "z"])
                              (.tuple [.binary .mul (.var "b7") (.var "lo"), .var "b7"])))))))))))) from rfl]
    simp only [recompose7ExprNat, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero, Nat.cast_one,
      TypedGadgets.qualifyName_u8Byte_check]
    refine mk_let_bind evZ ?_
    refine mk_let_bytes8 (n := zNat) (hhints.bytes8_typed zNat) (.var (by simp; rfl)) ?_
    exact mk_check_7bytes_false hbc htail
  | true =>
    rw [show (subBorrow56Fn true).body =
      .letValue (.bind "z") (.binary .add (.binary .sub (.var "x") (.var "y")) (.literal natLimit))
        (.letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                            .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
          (.hint (.array .field 8) (.var "z") "bytes_le")
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
              (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
                (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal 0])
                  (.letValue .wildcard
                    (.builtin (.assertEq (Lower.assertion "sub_borrow_56: b7 not boolean"))
                      [.binary .mul (.var "b7") (.binary .sub (.var "b7") (.literal 1)), .literal 0])
                    (.letValue (.bind "lo") recompose7ExprNat
                      (.letValue .wildcard
                        (.builtin (.assertEq (Lower.assertion "sub_borrow_56: recomposition failed"))
                          [.binary .add (.var "lo") (.binary .mul (.literal natLimit) (.var "b7")), .var "z"])
                        (.tuple [.binary .mul (.var "b7") (.var "lo"), .var "b7"]))))))))) from rfl]
    simp only [recompose7ExprNat, qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero, Nat.cast_one,
      TypedGadgets.qualifyName_u8_from_fields]
    refine mk_let_bind evZ ?_
    refine mk_let_bytes8 (n := zNat) (hhints.bytes8_typed zNat) (.var (by simp; rfl)) ?_
    exact mk_check_7bytes_true hbc htail

/-- Constructive forward derivation of `Prog::split_32_24(k)` for `k < 2^56`. -/
theorem evalFn_split_32_24_mk {w : World F} {usePair : Bool}
    (hbc : ByteCheckProvides w usePair) (hhints : Arith56HintsTyped w)
    (hprov : WorldProvidesFn w (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (k : Nat) (h : Heap F) (hk : k < natLimit) :
    EvalFn w (qualified "split_32_24") [.field (k : F)] h
      (.tuple [.field ((k % 4294967296 : Nat) : F), .field ((k / 4294967296 : Nat) : F)]) h := by
  apply EvalFn.intro (hprov [.field (k : F)] rfl)
  simp only [List.zip, List.zipWith]
  have hb7 : byteAt k 7 = 0 := byteAt_eq_zero (by unfold natLimit at hk; omega)
  have hloF :
      (byteAt k 0 : F) + (((256 : Nat) : F) * (byteAt k 1 : F) +
        (((65536 : Nat) : F) * (byteAt k 2 : F) + ((16777216 : Nat) : F) * (byteAt k 3 : F))) =
      ((k % 4294967296 : Nat) : F) := by
    have hnat : byteAt k 0 + (256 * byteAt k 1 + (65536 * byteAt k 2 + 16777216 * byteAt k 3)) =
        k % 4294967296 := by unfold byteAt; omega
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have hhiF :
      (byteAt k 4 : F) + (((256 : Nat) : F) * (byteAt k 5 : F) + ((65536 : Nat) : F) * (byteAt k 6 : F)) =
      ((k / 4294967296 : Nat) : F) := by
    have hnat : byteAt k 4 + (256 * byteAt k 5 + 65536 * byteAt k 6) = k / 4294967296 := by
      unfold byteAt natLimit at *; omega
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have hrecomp :
      ((k % 4294967296 : Nat) : F) + ((2 ^ 32 : Nat) : F) * ((k / 4294967296 : Nat) : F) = (k : F) := by
    have hnat : k % 4294967296 + 2 ^ 32 * (k / 4294967296) = k := by omega
    have := congrArg (Nat.cast : Nat → F) hnat
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have htail :
      EvalExpr w [] (bytes8Env F k ++ [("x", .field (k : F))])
        (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "split_32_24: top byte must be zero"))
          [.var "b7", .literal (0 : F)])
          (.letValue (.bind "lo")
            (.binary .add (.var "b0")
              (.binary .add (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1"))
                (.binary .add (.binary .mul (.literal ((65536 : Nat) : F)) (.var "b2"))
                  (.binary .mul (.literal ((16777216 : Nat) : F)) (.var "b3")))))
            (.letValue (.bind "hi")
              (.binary .add (.var "b4")
                (.binary .add (.binary .mul (.literal ((256 : Nat) : F)) (.var "b5"))
                  (.binary .mul (.literal ((65536 : Nat) : F)) (.var "b6"))))
              (.letValue .wildcard
                (.builtin (.assertEq (Lower.assertion "split_32_24: recomposition failed"))
                  [.binary .add (.var "lo") (.binary .mul (.literal ((2 ^ 32 : Nat) : F)) (.var "hi")), .var "x"])
                (.tuple [.var "lo", .var "hi"])))))
        h (.tuple [.field ((k % 4294967296 : Nat) : F), .field ((k / 4294967296 : Nat) : F)]) h := by
    refine mk_let_wild (mk_assertEq_field (.var (by simp [bytes8Env]; rfl)) (.literal (value := (0 : F))) (by simp [hb7])) ?_
    refine mk_let_bind (v := .field ((k % 4294967296 : Nat) : F)) ?_ ?_
    · rw [← hloF]
      exact mk_add (.var (by simp [bytes8Env]))
        (mk_add (mk_mul (.literal (value := ((256 : Nat) : F))) (.var (by simp [bytes8Env])))
          (mk_add (mk_mul (.literal (value := ((65536 : Nat) : F))) (.var (by simp [bytes8Env])))
            (mk_mul (.literal (value := ((16777216 : Nat) : F))) (.var (by simp [bytes8Env])))))
    · refine mk_let_bind (v := .field ((k / 4294967296 : Nat) : F)) ?_ ?_
      · rw [← hhiF]
        exact mk_add (.var (by simp [bytes8Env]))
          (mk_add (mk_mul (.literal (value := ((256 : Nat) : F))) (.var (by simp [bytes8Env])))
            (mk_mul (.literal (value := ((65536 : Nat) : F))) (.var (by simp [bytes8Env]))))
      · refine mk_let_wild (mk_assertEq_field
          (mk_add (.var (by simp)) (mk_mul (.literal (value := ((2 ^ 32 : Nat) : F))) (.var (by simp))))
          (.var (by simp [bytes8Env])) hrecomp) ?_
        exact .tuple (.cons (.var (by simp)) (.cons (.var (by simp)) .nil))
  cases usePair with
  | false =>
    rw [show (split32_24Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                    (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                      (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "split_32_24: top byte must be zero"))
                        [.var "b7", .literal 0])
                        (.letValue (.bind "lo")
                          (.binary .add (.var "b0")
                            (.binary .add (.binary .mul (.literal 256) (.var "b1"))
                              (.binary .add (.binary .mul (.literal 65536) (.var "b2"))
                                (.binary .mul (.literal 16777216) (.var "b3")))))
                          (.letValue (.bind "hi")
                            (.binary .add (.var "b4")
                              (.binary .add (.binary .mul (.literal 256) (.var "b5"))
                                (.binary .mul (.literal 65536) (.var "b6"))))
                            (.letValue .wildcard
                              (.builtin (.assertEq (Lower.assertion "split_32_24: recomposition failed"))
                                [.binary .add (.var "lo") (.binary .mul (.literal (2 ^ 32)) (.var "hi")), .var "x"])
                              (.tuple [.var "lo", .var "hi"])))))))))))) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8Byte_check]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    exact mk_check_7bytes_false hbc htail
  | true =>
    rw [show (split32_24Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
              (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "split_32_24: top byte must be zero"))
                  [.var "b7", .literal 0])
                  (.letValue (.bind "lo")
                    (.binary .add (.var "b0")
                      (.binary .add (.binary .mul (.literal 256) (.var "b1"))
                        (.binary .add (.binary .mul (.literal 65536) (.var "b2"))
                          (.binary .mul (.literal 16777216) (.var "b3")))))
                    (.letValue (.bind "hi")
                      (.binary .add (.var "b4")
                        (.binary .add (.binary .mul (.literal 256) (.var "b5"))
                          (.binary .mul (.literal 65536) (.var "b6"))))
                      (.letValue .wildcard
                        (.builtin (.assertEq (Lower.assertion "split_32_24: recomposition failed"))
                          [.binary .add (.var "lo") (.binary .mul (.literal (2 ^ 32)) (.var "hi")), .var "x"])
                        (.tuple [.var "lo", .var "hi"]))))))))) from rfl]
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
      TypedGadgets.qualifyName_u8_from_fields]
    refine mk_let_bytes8 (n := k) (hhints.bytes8_typed k) (.var (by simp; rfl)) ?_
    exact mk_check_7bytes_true hbc htail

/-- Constructive forward derivation of `Prog::mul_56(a, b)` for `a, b, a * b < 2^56`. -/
theorem evalFn_mul_56_mk {w : World F}
    (hsplit : ∀ (k : Nat), k < natLimit → ∀ h : Heap F,
      EvalFn w (qualified "split_32_24") [.field (k : F)] h
        (.tuple [.field ((k % 4294967296 : Nat) : F), .field ((k / 4294967296 : Nat) : F)]) h)
    (hu24 : ∀ (k : Nat), k < 16777216 → ∀ h : Heap F,
      EvalFn w (qualified "check_u24") [.field (k : F)] h (.tuple []) h)
    (hu56 : ∀ (k : Nat), k < natLimit → ∀ h : Heap F,
      EvalFn w (qualified "check_u56") [.field (k : F)] h (.tuple []) h)
    (hprov : WorldProvidesFn w (qualified "mul_56") ["x", "y"] (qualifyExprF F mul56Fn.body))
    (a b : Nat) (h : Heap F) (ha : a < natLimit) (hb : b < natLimit) (hab : a * b < natLimit) :
    EvalFn w (qualified "mul_56") [.field (a : F), .field (b : F)] h (.field ((a * b : Nat) : F)) h := by
  apply EvalFn.intro (hprov [.field (a : F), .field (b : F)] rfl)
  simp only [List.zip, List.zipWith]
  rw [show mul56Fn.body =
    .letValue (.tuple [.bind "xlo", .bind "xhi"]) (.call "split_32_24" (some []) [.var "x"])
      (.letValue (.tuple [.bind "ylo", .bind "yhi"]) (.call "split_32_24" (some []) [.var "y"])
        (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "mul_56: high product overflow"))
          [.binary .mul (.var "xhi") (.var "yhi"), .literal 0])
          (.letValue (.bind "mid")
            (.binary .add (.binary .mul (.var "xlo") (.var "yhi")) (.binary .mul (.var "xhi") (.var "ylo")))
            (.letValue .wildcard (.call "check_u24" (some []) [.var "mid"])
              (.letValue (.bind "lo") (.binary .mul (.var "xlo") (.var "ylo"))
                (.letValue .wildcard (.call "check_u56" (some []) [.var "lo"])
                  (.letValue (.bind "prod")
                    (.binary .add (.var "lo") (.binary .mul (.literal (2 ^ 32)) (.var "mid")))
                    (.letValue .wildcard (.call "check_u56" (some []) [.var "prod"]) (.var "prod"))))))))) from rfl]
  simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
    Option.map_some, List.map, Nat.cast_zero, TypedGadgets.qualifyName_split_32_24,
    TypedGadgets.qualifyName_check_u24, TypedGadgets.qualifyName_check_u56]
  let alo : Nat := a % 4294967296
  let ahi : Nat := a / 4294967296
  let blo : Nat := b % 4294967296
  let bhi : Nat := b / 4294967296
  have ha_eq : a = alo + 4294967296 * ahi := by dsimp only [alo, ahi]; omega
  have hb_eq : b = blo + 4294967296 * bhi := by dsimp only [blo, bhi]; omega
  have hprod_eq : a * b = alo * blo + 4294967296 * (alo * bhi + ahi * blo) +
      4294967296 * 4294967296 * (ahi * bhi) := by
    rw [ha_eq, hb_eq]; ring
  have hhi0 : ahi * bhi = 0 := by
    by_contra hne
    have hge1 : 1 ≤ ahi * bhi := Nat.pos_of_ne_zero hne
    have hbig : 4294967296 * 4294967296 ≤ a * b := by
      have h1 : 4294967296 * 4294967296 * 1 ≤ 4294967296 * 4294967296 * (ahi * bhi) :=
        Nat.mul_le_mul_left _ hge1
      omega
    unfold natLimit at hab; omega
  let mid : Nat := alo * bhi + ahi * blo
  let lo : Nat := alo * blo
  have hprod_ab : lo + 4294967296 * mid = a * b := by
    dsimp only [lo, mid]; rw [hprod_eq, hhi0]; ring
  have hmid_lt : mid < 16777216 := by unfold natLimit at hab; omega
  have hlo_lt : lo < natLimit := by omega
  have hhi0F : (ahi : F) * (bhi : F) = (0 : F) := by
    have := congrArg (Nat.cast : Nat → F) hhi0
    simpa [Nat.cast_mul] using this
  have hmidF : (alo : F) * (bhi : F) + (ahi : F) * (blo : F) = (mid : F) := by
    simp [mid, Nat.cast_add, Nat.cast_mul]
  have hloF : (alo : F) * (blo : F) = (lo : F) := by
    simp [lo, Nat.cast_mul]
  have hprodF : (lo : F) + ((2 ^ 32 : Nat) : F) * (mid : F) = ((a * b : Nat) : F) := by
    have := congrArg (Nat.cast : Nat → F) hprod_ab
    simpa [Nat.cast_add, Nat.cast_mul] using this
  refine mk_let_tuple2 (.call (.cons (.var (by simp)) .nil) (hsplit a ha h)) ?_
  refine mk_let_tuple2 (.call (.cons (.var (by simp)) .nil) (hsplit b hb h)) ?_
  refine mk_let_wild (mk_assertEq_field (mk_mul (.var (by simp [ahi])) (.var (by simp [bhi]))) (.literal (value := (0 : F))) hhi0F) ?_
  refine mk_let_bind (v := .field (mid : F))
    (by rw [← hmidF]; exact mk_add (mk_mul (.var (by simp [alo])) (.var (by simp [bhi]))) (mk_mul (.var (by simp [ahi])) (.var (by simp [blo])))) ?_
  refine mk_let_wild (.call (.cons (.var (by simp)) .nil) (hu24 mid hmid_lt h)) ?_
  refine mk_let_bind (v := .field (lo : F))
    (by rw [← hloF]; exact mk_mul (.var (by simp [alo])) (.var (by simp [blo]))) ?_
  refine mk_let_wild (.call (.cons (.var (by simp)) .nil) (hu56 lo hlo_lt h)) ?_
  refine mk_let_bind (v := .field ((a * b : Nat) : F))
    (by rw [← hprodF]; exact mk_add (.var (by simp)) (mk_mul (.literal (value := ((2 ^ 32 : Nat) : F))) (.var (by simp)))) ?_
  refine mk_let_wild (.call (.cons (.var (by simp)) .nil) (hu56 (a * b) hab h)) ?_
  exact .var (by simp)

/-- Constructive forward derivation of `Prog::divmod_56(a, b)` for `a < 2^56`, `0 < b < 2^56`. -/
theorem evalFn_divmod_56_mk {w : World F}
    (hhints : Arith56HintsTyped w)
    (hmul : ∀ a b : Nat, a < natLimit → b < natLimit → a * b < natLimit → ∀ h : Heap F,
      EvalFn w (qualified "mul_56") [.field (a : F), .field (b : F)] h (.field ((a * b : Nat) : F)) h)
    (hu56 : ∀ (k : Nat), k < natLimit → ∀ h : Heap F,
      EvalFn w (qualified "check_u56") [.field (k : F)] h (.tuple []) h)
    (hsub : ∀ a b : Nat, a < natLimit → b < natLimit → ∀ h : Heap F,
      EvalFn w (qualified "sub_borrow_56") [.field (a : F), .field (b : F)] h
        (.tuple [.field ((a - b : Nat) : F), .field ((if b ≤ a then 1 else 0 : Nat) : F)]) h)
    (hprov : WorldProvidesFn w (qualified "divmod_56") ["x", "y"] (qualifyExprF F divmod56Fn.body))
    (a b : Nat) (h : Heap F) (ha : a < natLimit) (hbPos : 0 < b) (hb : b < natLimit) :
    EvalFn w (qualified "divmod_56") [.field (a : F), .field (b : F)] h
      (.tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)]) h := by
  apply EvalFn.intro (hprov [.field (a : F), .field (b : F)] rfl)
  simp only [List.zip, List.zipWith]
  rw [show divmod56Fn.body =
    .letValue (.tuple [.bind "q", .bind "r"])
      (.hint (.tuple [.field, .field]) (.tuple [.var "x", .var "y"]) "ixcc.divmod")
      (.letValue (.bind "p") (.call "mul_56" (some []) [.var "q", .var "y"])
        (.letValue .wildcard (.call "check_u56" (some []) [.var "r"])
          (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "divmod_56: q*y + r = x"))
            [.binary .add (.var "p") (.var "r"), .var "x"])
            (.letValue (.tuple [.wildcard, .bind "ge"]) (.call "sub_borrow_56" (some []) [.var "r", .var "y"])
              (.letValue .wildcard (.builtin (.assertEq (Lower.assertion "divmod_56: r < y")) [.var "ge", .literal 0])
                (.tuple [.var "q", .var "r"])))))) from rfl]
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, Option.map_some, List.map, Nat.cast_zero,
    TypedGadgets.qualifyName_mul_56, TypedGadgets.qualifyName_check_u56,
    TypedGadgets.qualifyName_sub_borrow_56]
  let q : Nat := a / b
  let r : Nat := a % b
  have hqLt : q < natLimit := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
  have hrLtB : r < b := Nat.mod_lt a hbPos
  have hrLt : r < natLimit := Nat.lt_trans hrLtB hb
  have hdiv : q * b + r = a := by
    dsimp only [q, r]; rw [Nat.mul_comm]; exact Nat.div_add_mod a b
  have hqbLt : q * b < natLimit := by omega
  have hdivF : ((q * b : Nat) : F) + (r : F) = (a : F) := by
    have := congrArg (Nat.cast : Nat → F) hdiv
    simpa [Nat.cast_add, Nat.cast_mul] using this
  have hsubR : EvalFn w (qualified "sub_borrow_56") [.field (r : F), .field (b : F)] h
      (.tuple [.field ((r - b : Nat) : F), .field (0 : F)]) h := by
    have hnot : ¬ (b ≤ r) := by omega
    simpa [hnot] using hsub r b hrLt hb h
  refine mk_let_tuple2
    (by
      rw [← tuple2Const_toValue (F := F) q r]
      exact .hint (.tuple (.cons (.var (by simp; rfl)) (.cons (.var (by simp; rfl)) .nil)))
        (hhints.tuple2_typed q r)) ?_
  refine mk_let_bind (.call (.cons (.var (by simp)) (.cons (.var (by simp)) .nil))
    (hmul q b hqLt hb hqbLt h)) ?_
  refine mk_let_wild (.call (.cons (.var (by simp)) .nil) (hu56 r hrLt h)) ?_
  refine mk_let_wild (mk_assertEq_field (mk_add (.var (by simp)) (.var (by simp))) (.var (by simp)) hdivF) ?_
  refine mk_let_tuple2_wild1 (.call (.cons (.var (by simp)) (.cons (.var (by simp)) .nil)) hsubR) ?_
  refine mk_let_wild (mk_assertEq_field (.var (by simp)) (.literal (value := (0 : F))) rfl) ?_
  exact .tuple (.cons (.var (by simp [q])) (.cons (.var (by simp [r])) .nil))

/-- Constructive forward derivation of `Fields::is_zero(k)` for `k < 2^56` under `FieldCompatible64 F`. -/
theorem evalFn_fields_is_zero_mk (fc : FieldCompatible64 F) {w : World F}
    (hprov : WorldProvidesFn w "Fields::is_zero" ["x"]
      (Aiur.Generic.Expr.matchValue (.var "x")
        [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))]))
    (k : Nat) (h : Heap F) (hk : k < natLimit) :
    EvalFn w "Fields::is_zero" [.field (k : F)] h
      (.field ((if k == 0 then 1 else 0 : Nat) : F)) h := by
  apply EvalFn.intro (hprov [.field (k : F)] rfl)
  by_cases hk0 : k = 0
  · subst hk0
    have hsel : SourceSemantics.selectArm w [] h (.field ((0 : Nat) : F))
        [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))] =
        .ok (some ([], .literal (1 : F))) := by
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings]
    simpa using EvalExpr.matchValue (.var (by simp)) hsel EvalExpr.literal
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hne : (0 : F) ≠ (k : F) := Ne.symm (fc.ne_zero_of_pos56 hkPos hk)
    have hsel : SourceSemantics.selectArm w [] h (.field (k : F))
        [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))] =
        .ok (some ([], .literal (0 : F))) := by
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings, hne]
    have hbeq : (k == 0) = false := beq_false_of_ne hk0
    simpa [hbeq] using EvalExpr.matchValue (.var (by simp)) hsel EvalExpr.literal

mutual

private theorem callsAny_mono {ns1 ns2 : List String} (hsub : ∀ s ∈ ns1, s ∈ ns2) :
    ∀ e : Expr, callsAny ns1 e = true → callsAny ns2 e = true
  | .call nm _ xs, h => by
    simp only [callsAny, Bool.or_eq_true, List.contains_iff_mem] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hsub nm h1)
    · exact Or.inr (callsAnyList_mono hsub xs h2)
  | .literal _, h | .var _, h | .global _ _, h | .control _ _, h => by cases h
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h => callsAnyList_mono hsub xs h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h => callsAny_mono hsub x h
  | .letValue _ x b, h | .binary _ x b, h => by
    simp only [callsAny, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (callsAny_mono hsub x h1)
    · exact Or.inr (callsAny_mono hsub b h2)
  | .matchValue x arms, h => by
    simp only [callsAny, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (callsAny_mono hsub x h1)
    · exact Or.inr (callsAnyArms_mono hsub arms h2)

private theorem callsAnyList_mono {ns1 ns2 : List String} (hsub : ∀ s ∈ ns1, s ∈ ns2) :
    ∀ xs : List Expr, callsAnyList ns1 xs = true → callsAnyList ns2 xs = true
  | [], h => by cases h
  | x :: xs, h => by
    simp only [callsAnyList, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (callsAny_mono hsub x h1)
    · exact Or.inr (callsAnyList_mono hsub xs h2)

private theorem callsAnyArms_mono {ns1 ns2 : List String} (hsub : ∀ s ∈ ns1, s ∈ ns2) :
    ∀ arms : List (Pat × Expr), callsAnyArms ns1 arms = true → callsAnyArms ns2 arms = true
  | [], h => by cases h
  | (_, b) :: rest, h => by
    simp only [callsAnyArms, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (callsAny_mono hsub b h1)
    · exact Or.inr (callsAnyArms_mono hsub rest h2)

end

/-- End-to-end constructive builder of `Arith56WorldSpec fns w` from demand-guarded
`WorldProvidesFn` bindings, `ByteCheckProvides`, `Arith56HintsTyped`, and `FieldCompatible64 F`. -/
theorem arith56WorldSpec_of_world (fc : FieldCompatible64 F) {fns : List Fn} {w : World F}
    {usePair : Bool}
    (hbc : ByteCheckProvides w usePair) (hhints : Arith56HintsTyped w)
    (hU8 : (∃ f ∈ fns, callsAny ["check_u8"] f.body = true) →
      WorldProvidesFn w (qualified "check_u8") ["x"] (qualifyExprF F (checkU8Fn usePair).body))
    (hU16 : (∃ f ∈ fns, callsAny ["check_u16"] f.body = true) →
      WorldProvidesFn w (qualified "check_u16") ["x"] (qualifyExprF F (checkU16Fn usePair).body))
    (hU24 : (∃ f ∈ fns, callsAny ["check_u24", "mul_56", "divmod_56"] f.body = true) →
      WorldProvidesFn w (qualified "check_u24") ["x"] (qualifyExprF F (checkU24Fn usePair).body))
    (hU56 : (∃ f ∈ fns, callsAny ["check_u56", "mul_56", "divmod_56"] f.body = true) →
      WorldProvidesFn w (qualified "check_u56") ["x"] (qualifyExprF F (checkU56Fn usePair).body))
    (hSub : (∃ f ∈ fns, callsAny ["sub_borrow_56", "divmod_56"] f.body = true) →
      WorldProvidesFn w (qualified "sub_borrow_56") ["x", "y"]
        (qualifyExprF F (subBorrow56Fn usePair).body))
    (hSplit : (∃ f ∈ fns, callsAny ["split_32_24", "mul_56", "divmod_56"] f.body = true) →
      WorldProvidesFn w (qualified "split_32_24") ["x"] (qualifyExprF F (split32_24Fn usePair).body))
    (hMul : (∃ f ∈ fns, callsAny ["mul_56", "divmod_56"] f.body = true) →
      WorldProvidesFn w (qualified "mul_56") ["x", "y"] (qualifyExprF F mul56Fn.body))
    (hDiv : (∃ f ∈ fns, callsAny ["divmod_56"] f.body = true) →
      WorldProvidesFn w (qualified "divmod_56") ["x", "y"] (qualifyExprF F divmod56Fn.body))
    (hIsZero : (∃ f ∈ fns, callsAny ["Fields::is_zero"] f.body = true) →
      WorldProvidesFn w "Fields::is_zero" ["x"]
        (Aiur.Generic.Expr.matchValue (.var "x")
          [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))])) :
    Arith56WorldSpec fns w where
  check_u8 hc k h hk := evalFn_check_u8_mk hbc (hU8 hc) k h hk
  check_u16 hc k h hk := evalFn_check_u16_mk hbc hhints (hU16 hc) k h hk
  check_u24 hc k h hk :=
    evalFn_check_u24_mk hbc hhints
      (hU24 (let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩)) k h hk
  check_u56 hc k h hk :=
    evalFn_check_u56_mk hbc hhints
      (hU56 (let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩)) k h hk
  sub_borrow_56 hc a b h ha hb :=
    evalFn_sub_borrow_56_mk hbc hhints
      (hSub (let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩)) a b h ha hb
  split_32_24 hc k h hk :=
    evalFn_split_32_24_mk hbc hhints
      (hSplit (let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩)) k h hk
  mul_56 hc a b h ha hb hab :=
    let hc3 : ∃ f ∈ fns, callsAny ["check_u24", "mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hc56 : ∃ f ∈ fns, callsAny ["check_u56", "mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hcSp : ∃ f ∈ fns, callsAny ["split_32_24", "mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hcM : ∃ f ∈ fns, callsAny ["mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    evalFn_mul_56_mk
      (fun k hk hh => evalFn_split_32_24_mk hbc hhints (hSplit hcSp) k hh hk)
      (fun k hk hh => evalFn_check_u24_mk hbc hhints (hU24 hc3) k hh hk)
      (fun k hk hh => evalFn_check_u56_mk hbc hhints (hU56 hc56) k hh hk)
      (hMul hcM) a b h ha hb hab
  divmod_56 hc a b h ha hbPos hb :=
    let hc3 : ∃ f ∈ fns, callsAny ["check_u24", "mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hc56 : ∃ f ∈ fns, callsAny ["check_u56", "mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hcSp : ∃ f ∈ fns, callsAny ["split_32_24", "mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hcSub : ∃ f ∈ fns, callsAny ["sub_borrow_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    let hcM : ∃ f ∈ fns, callsAny ["mul_56", "divmod_56"] f.body = true :=
      let ⟨f, hf, hcf⟩ := hc; ⟨f, hf, callsAny_mono (by simp) _ hcf⟩
    evalFn_divmod_56_mk hhints
      (fun x y hx hy hxy hh =>
        evalFn_mul_56_mk
          (fun k hk h0 => evalFn_split_32_24_mk hbc hhints (hSplit hcSp) k h0 hk)
          (fun k hk h0 => evalFn_check_u24_mk hbc hhints (hU24 hc3) k h0 hk)
          (fun k hk h0 => evalFn_check_u56_mk hbc hhints (hU56 hc56) k h0 hk)
          (hMul hcM) x y hh hx hy hxy)
      (fun k hk hh => evalFn_check_u56_mk hbc hhints (hU56 hc56) k hh hk)
      (fun x y hx hy hh => evalFn_sub_borrow_56_mk hbc hhints (hSub hcSub) x y hh hx hy)
      (hDiv hc) a b h ha hbPos hb
  fields_is_zero hc k h hk := evalFn_fields_is_zero_mk fc (hIsZero hc) k h hk

end Arith56Helpers

/-! ## Section 6: Main Mutual Backward Simulation & Top-Level Composition -/

section BackwardSim

variable {F : Type} [Field F] [DecidableEq F]

/-! ### Syntactic & Environment Helpers -/

mutual

theorem isCleanExpr_imp_isPlainExpr : ∀ e : Expr, isCleanExpr e = true → isPlainExpr e = true
  | .literal _, _ | .var _, _ => rfl
  | .global _ _, h | .control _ _, h => by cases h
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h | .call _ _ xs, h =>
    isCleanList_imp_isPlainList xs h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    isCleanExpr_imp_isPlainExpr x h
  | .binary _ l r, h => by
    simp only [isCleanExpr, isPlainExpr, Bool.and_eq_true] at h ⊢
    exact ⟨isCleanExpr_imp_isPlainExpr l h.1, isCleanExpr_imp_isPlainExpr r h.2⟩
  | .letValue _ rhs body, h => by
    simp only [isCleanExpr, isPlainExpr, Bool.and_eq_true] at h ⊢
    exact ⟨isCleanExpr_imp_isPlainExpr rhs h.1.2, isCleanExpr_imp_isPlainExpr body h.2⟩
  | .matchValue scrut arms, h => by
    simp only [isCleanExpr, isPlainExpr, Bool.and_eq_true] at h ⊢
    exact ⟨isCleanExpr_imp_isPlainExpr scrut h.1, isCleanArms_imp_isPlainArms arms h.2⟩

theorem isCleanList_imp_isPlainList : ∀ xs : List Expr, isCleanList xs = true → isPlainList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanList, isPlainList, Bool.and_eq_true] at h ⊢
    exact ⟨isCleanExpr_imp_isPlainExpr x h.1, isCleanList_imp_isPlainList xs h.2⟩

theorem isCleanArms_imp_isPlainArms :
    ∀ arms : List (Pat × Expr), isCleanArms arms = true → isPlainArms arms = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [isCleanArms, isPlainArms, Bool.and_eq_true] at h ⊢
    exact ⟨isCleanExpr_imp_isPlainExpr b h.1.2, isCleanArms_imp_isPlainArms rest h.2⟩

end

omit [Field F] [DecidableEq F] in
theorem notPEGe_of_not_hasPEPrefix {y : String} (h : hasPEPrefix y = false) : NotPEGe 0 y := by
  intro n _ heq
  subst heq
  rw [hasPEPrefix_peVarName] at h
  cases h

omit [Field F] [DecidableEq F] in
theorem qualifyName_of_noDoubleColon {nm : String} (h : hasDoubleColon nm.toList = false) :
    qualifyName nm = qualified nm := by
  unfold qualifyName
  simp [h]

omit [Field F] [DecidableEq F] in
theorem callsAnyArms_of_mem {ns : List String} {p : Pat} {b : Expr} {arms : List (Pat × Expr)}
    (hmem : (p, b) ∈ arms) (hcall : callsAny ns b = true) :
    callsAnyArms ns arms = true := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    simp only [callsAnyArms, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with heq | htl
    · cases heq; exact Or.inl hcall
    · exact Or.inr (ih htl)

omit [Field F] [DecidableEq F] in
theorem mem_fns_of_mem_fnMap {fns : List Fn} {nm : String} {callee : Fn}
    (h : (nm, callee) ∈ fns.map fun f => (f.name, f)) :
    callee ∈ fns ∧ callee.name = nm := by
  obtain ⟨g, hg, heq⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨hg, rfl⟩

omit [Field F] [DecidableEq F] in
theorem peFn_name (cfg : PEConfig) (fnMap : List (String × Fn)) (f : Fn) :
    (peFn cfg fnMap f).name = f.name := by
  unfold peFn; split <;> rfl

omit [Field F] [DecidableEq F] in
theorem peFn_params (cfg : PEConfig) (fnMap : List (String × Fn)) (f : Fn) :
    (peFn cfg fnMap f).params = f.params := by
  unfold peFn; split <;> rfl

omit [Field F] [DecidableEq F] in
theorem partialEvalFns_map_name (cfg : PEConfig) (fns : List Fn) :
    (partialEvalFns cfg fns).map (·.name) = fns.map (·.name) := by
  unfold partialEvalFns
  rw [List.map_map]
  exact List.map_congr_left fun f _ => peFn_name cfg _ f

omit [DecidableEq F] in
theorem map_qualifyArms (arms : List (Pat × Expr)) :
    ((arms.map fun (p, b) => (qualifyPat p, qualifyExpr b)).map
        fun (p, b) => (Aiur.Generic.Pattern.map (Nat.cast : Nat → F) p,
          Aiur.Generic.Expr.map (Nat.cast : Nat → F) b)) =
      arms.map fun (p, b) => (qualifyPatF F p, qualifyExprF F b) := by
  induction arms with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨p, b⟩
    simp only [List.map_cons, qualifyPatF, qualifyExprF, ih]

theorem evalLetsN_emitResidual_inv {w : World F} {d : Nat}
    {loc0 loc2 : Environment F Nat} {bs : LetBinds} {rhs : Expr} {st : PEState}
    {h0 h2 : Heap F}
    (ev : EvalLetsN w d loc0 (emitResidual bs rhs st).1.1 h0 loc2 h2) :
    ∃ locM hM rOpt,
      EvalLetsN w d loc0 bs h0 locM hM ∧
      EvalExprN w d [] locM (qualifyExprF F rhs) hM rOpt h2 ∧
      loc2.find? (·.1 == peVarName st.nextId) = some (peVarName st.nextId, rOpt) := by
  simp only [emitResidual, allocFresh] at ev
  obtain ⟨locM, hM, evBs, evLast⟩ := ev.split_append
  cases evLast with
  | cons evRhs hm evNil =>
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm
    cases evNil
    exact ⟨locM, hM, _, evBs, evRhs, by simp⟩

/-! ### Core Mutual Backward Simulation (`peExpr_backward`, `peExprList_backward`, `peArms_backward`) -/

set_option maxHeartbeats 2400000 in
mutual

theorem peExpr_backward (fc : FieldCompatible64 F) (cfg : PEConfig) (fns : List Fn)
    {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (harith : Arith56WorldSpec fns wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (e : Expr) (st : PEState)
      {locOpt locOpt' locOrig : Environment F Nat} {hOpt1 hOpt2 hOrig1 : Heap F},
      isCleanExpr e = true →
      scopedExpr (senv.map Prod.fst) e = true →
      (∀ nm, callsAny [nm] e = true → ∃ f ∈ fns, callsAny [nm] f.body = true) →
      SEnvNotPEGe st.nextId senv →
      EnvDenotes hOpt1 hOrig1 locOpt senv locOrig →
      EvalLetsN wOpt d locOpt
        (peExpr cfg (fns.map fun f => (f.name, f)) fuel curFn dynFns senv e st).1.1
        hOpt1 locOpt' hOpt2 →
      ∃ vOrig hOrig2,
        EvalExpr wOrig [] locOrig (qualifyExprF F e) hOrig1 vOrig hOrig2 ∧
        SValDenotes hOpt2 hOrig2 locOpt'
          (peExpr cfg (fns.map fun f => (f.name, f)) fuel curFn dynFns senv e st).1.2 vOrig
  | _, _, _, _, .literal n, st, _, _, _, _, _, _, _, _, _, _, _, ev => by
    rw [peExpr] at ev ⊢
    by_cases hlt : n < natLimit
    · simp only [hlt, ↓reduceIte] at ev ⊢
      cases ev
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
      exact ⟨.field (n : F), _, .literal, ⟨hlt, rfl⟩⟩
    · simp only [hlt, ↓reduceIte] at ev ⊢
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
      cases evBs
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      cases evRhs
      exact ⟨.field (n : F), _, .literal, ⟨.field (n : F), hfind, by rw [ValEq]⟩⟩
  | _, _, _, senv, .var x, st, _, _, _, _, _, _, _, hsc, _, _, henv, ev => by
    rw [peExpr] at ev ⊢
    cases hl : senv.lookup x with
    | none =>
      exact absurd hl (lookup_ne_none_of_mem_map_fst (List.contains_iff_mem.mp hsc))
    | some sv =>
      rw [hl] at ev; dsimp only at ev ⊢
      cases ev
      obtain ⟨vOrig, hfindOrig, hsv⟩ := henv x sv hl
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
      exact ⟨vOrig, _, .var hfindOrig, hsv⟩
  | _, _, _, _, .global _ _, _, _, _, _, _, _, _, hc, _, _, _, _, _ => by cases hc
  | _, _, _, _, .control _ _, _, _, _, _, _, _, _, hc, _, _, _, _, _ => by cases hc
  | fuel, cur, dyn, senv, .tuple xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
      peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
    rw [h1] at hvs; dsimp only at hvs
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
    rw [map_qualifyExpr_map_cast]
    exact ⟨.tuple vsOrig, hOrig2, .tuple evArgs, ⟨vsOrig, rfl, hvs⟩⟩
  | fuel, cur, dyn, senv, .array xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
      peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
    rw [h1] at hvs; dsimp only at hvs
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
    rw [map_qualifyExpr_map_cast]
    exact ⟨.tuple vsOrig, hOrig2, .array evArgs, ⟨vsOrig, rfl, hvs⟩⟩
  | fuel, cur, dyn, senv, .construct en targs c xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    cases targs with
    | some ts =>
      cases ts with
      | nil =>
        dsimp only at ev ⊢
        obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
          peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
        rw [h1] at hvs; dsimp only at hvs
        simp only [qualifyExprF, qualifyExpr, Option.map_some, List.map_nil, Aiur.Generic.Expr.map]
        rw [map_qualifyExpr_map_cast]
        exact ⟨_, hOrig2, .construct evArgs, ⟨vsOrig, by rw [instanceName_nil], hvs⟩⟩
      | cons t ts =>
        dsimp only at ev ⊢
        obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
        obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
          peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
        rw [h1] at hvs; dsimp only at hvs
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
        rw [map_qualifyExpr_map_cast] at evRhs ⊢
        cases evRhs with
        | construct hargs =>
          have hveq := evalArgsN_reifySValList_backward hvs hargs
          exact ⟨_, hOrig2, .construct evArgs, ⟨_, hfind, by rw [ValEq]; exact ⟨rfl, rfl, hveq⟩⟩⟩
    | none =>
      dsimp only at ev ⊢
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
      obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
        peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hvs; dsimp only at hvs
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      rw [map_qualifyExpr_map_cast] at evRhs ⊢
      cases evRhs with
      | construct hargs =>
        have hveq := evalArgsN_reifySValList_backward hvs hargs
        exact ⟨_, hOrig2, .construct evArgs, ⟨_, hfind, by rw [ValEq]; exact ⟨rfl, rfl, hveq⟩⟩⟩
  | fuel, cur, dyn, senv, .constructAs ps ty c xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
      peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hvs; dsimp only at hvs
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    rw [map_qualifyExpr_map_cast] at evRhs ⊢
    cases evRhs with
    | constructAs hargs =>
      have hveq := evalArgsN_reifySValList_backward hvs hargs
      exact ⟨_, hOrig2, .constructAs evArgs, ⟨_, hfind, by rw [ValEq]; exact ⟨rfl, rfl, hveq⟩⟩⟩
  | fuel, cur, dyn, senv, .record hd xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
      peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hvs; dsimp only at hvs
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    rw [map_qualifyExpr_map_cast] at evRhs ⊢
    cases evRhs with
    | record hargs =>
      have hveq := evalArgsN_reifySValList_backward hvs hargs
      exact ⟨_, hOrig2, .record evArgs,
        ⟨_, hfind, by rw [ValEq]; exact ⟨rfl, rfl, recordHead_order_valEq _ hveq (by simp [ValEq, ValEqList])⟩⟩⟩
  | fuel, cur, dyn, senv, .update ps xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
      peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hvs; dsimp only at hvs
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    rw [map_qualifyExpr_map_cast] at evRhs ⊢
    cases evRhs with
    | update hargs hu =>
      have hveq := evalArgsN_reifySValList_backward hvs hargs
      obtain ⟨rOrig, hu', hr⟩ := update_value_valEq hveq hu
      exact ⟨rOrig, hOrig2, .update evArgs hu', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .repeat x n, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hsv; dsimp only at hsv
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    cases evRhs with
    | «repeat» evRe =>
      have hveq := evalExprN_reifySVal_backward hsv evRe
      exact ⟨.tuple (List.replicate n vOrig), hOrig2, .repeat evX,
        ⟨_, hfind, by rw [ValEq, valEqList_iff_forall₂]; exact forall₂_replicate hveq n⟩⟩
  | fuel, cur, dyn, senv, .slice x s t, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hsv; dsimp only at hsv
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    cases evRhs with
    | slice evRe hs =>
      have hveq := evalExprN_reifySVal_backward hsv evRe
      obtain ⟨rOrig, hs', hr⟩ := sliceValue_valEq hveq hs
      exact ⟨rOrig, hOrig2, .slice evX hs', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .member x fld, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hsv; dsimp only at hsv
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    cases evRhs with
    | member evRe hm =>
      have hveq := evalExprN_reifySVal_backward hsv evRe
      obtain ⟨rOrig, hm', hr⟩ := memberValue_valEq hveq hm
      exact ⟨rOrig, hOrig2, .member evX hm', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .store x, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨vOrig, hOrigM, evX, hsv⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
    rw [h1] at hsv; dsimp only at hsv
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
    refine ⟨.ptr vOrig.type hOrigM.length, hOrigM ++ [vOrig], .store evX, ?_⟩
    exact ⟨vOrig.type, hOrigM.length, vOrig, rfl, by simp, rfl,
      hsv.mono_heaps (Heap.Extends.refl _) (Heap.Extends.append_right _ _)⟩
  | fuel, cur, dyn, senv, .load x, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    cases sv with
    | ptr inner =>
      dsimp only at ev ⊢
      obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
      rw [h1] at hsv; dsimp only at hsv
      rcases hsv with ⟨t, a, wOrig, rfl, ha, hty, hw⟩
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
      exact ⟨wOrig, hOrig2, .load evX (by simp [loadValue, ha, hty]), hw⟩
    | lit _ | subLit _ _ | var _ | tuple _ | array _ | ctor _ _ _ =>
      dsimp only at ev ⊢
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
      obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hsv; dsimp only at hsv
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      cases evRhs with
      | load evRe hl =>
        have hveq := evalExprN_reifySVal_backward hsv evRe
        obtain ⟨rOrig, hl', hr⟩ := loadValue_valEq hveq hl
        exact ⟨rOrig, hOrig2, .load evX hl', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .project x i, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    cases sv with
    | tuple svs | array svs =>
      dsimp only at ev ⊢
      cases hi : svs[i]? with
      | some svi =>
        rw [hi] at ev; dsimp only at ev ⊢
        obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
        rw [h1] at hsv; dsimp only at hsv
        rcases hsv with ⟨vs, rfl, hvs⟩
        obtain ⟨vi, hvi, hviDen⟩ := svalListDenotes_getElem?_some hvs hi
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
        exact ⟨vi, hOrig2, .project evX (by simp [projectValue, hvi]), hviDen⟩
      | none =>
        rw [hi] at ev; dsimp only at ev ⊢
        obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
        obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
        rw [h1] at hsv; dsimp only at hsv
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
        cases evRhs with
        | project evRe hp =>
          have hveq := evalExprN_reifySVal_backward hsv evRe
          obtain ⟨rOrig, hp', hr⟩ := projectValue_valEq hveq hp
          exact ⟨rOrig, hOrig2, .project evX hp', ⟨_, hfind, hr⟩⟩
    | lit _ | subLit _ _ | var _ | ctor _ _ _ | ptr _ =>
      dsimp only at ev ⊢
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
      obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hsv; dsimp only at hsv
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      cases evRhs with
      | project evRe hp =>
        have hveq := evalExprN_reifySVal_backward hsv evRe
        obtain ⟨rOrig, hp', hr⟩ := projectValue_valEq hveq hp
        exact ⟨rOrig, hOrig2, .project evX hp', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .index x i, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    cases sv with
    | tuple svs | array svs =>
      dsimp only at ev ⊢
      cases hi : svs[i]? with
      | some svi =>
        rw [hi] at ev; dsimp only at ev ⊢
        obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
        rw [h1] at hsv; dsimp only at hsv
        rcases hsv with ⟨vs, rfl, hvs⟩
        obtain ⟨vi, hvi, hviDen⟩ := svalListDenotes_getElem?_some hvs hi
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
        exact ⟨vi, hOrig2, .index evX (by simp [projectValue, hvi]), hviDen⟩
      | none =>
        rw [hi] at ev; dsimp only at ev ⊢
        obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
        obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
        rw [h1] at hsv; dsimp only at hsv
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
        cases evRhs with
        | index evRe hp =>
          have hveq := evalExprN_reifySVal_backward hsv evRe
          obtain ⟨rOrig, hp', hr⟩ := projectValue_valEq hveq hp
          exact ⟨rOrig, hOrig2, .index evX hp', ⟨_, hfind, hr⟩⟩
    | lit _ | subLit _ _ | var _ | ctor _ _ _ | ptr _ =>
      dsimp only at ev ⊢
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
      obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hsv; dsimp only at hsv
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      cases evRhs with
      | index evRe hp =>
        have hveq := evalExprN_reifySVal_backward hsv evRe
        obtain ⟨rOrig, hp', hr⟩ := projectValue_valEq hveq hp
        exact ⟨rOrig, hOrig2, .index evX hp', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .hint ty k ch, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv k st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
    obtain ⟨vOrig, hOrig2, evK, hsv⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv k st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
    rw [h1] at hsv; dsimp only at hsv
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
    cases evRhs with
    | hint evRe ht =>
      exact ⟨_, hOrig2, .hint evK (by rw [← haux.typed_eq]; exact ht),
        ⟨_, hfind, ValEq.refl_of_pointerFree (Constant.toValue_pointerFree _)⟩⟩
  | fuel, cur, dyn, senv, .neg x, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨bs, sv⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    cases sv with
    | lit n =>
      cases n with
      | zero =>
        obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
        rw [h1] at hsv; dsimp only at hsv
        rcases hsv with ⟨h0, rfl⟩
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
        exact ⟨.field ((0 : Nat) : F), hOrig2, .neg evX (by simp [evalNeg]), ⟨h0, rfl⟩⟩
      | succ m =>
        obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
        obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
        rw [h1] at hsv; dsimp only at hsv
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
        cases evRhs with
        | neg evRe hop =>
          have hveq := evalExprN_reifySVal_backward hsv evRe
          obtain ⟨hop', hr⟩ := evalNeg_valEq hveq hop
          exact ⟨_, hOrig2, .neg evX hop', ⟨_, hfind, hr⟩⟩
    | subLit _ _ | var _ | tuple _ | array _ | ctor _ _ _ | ptr _ =>
      dsimp only at ev ⊢
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv ev
      obtain ⟨vOrig, hOrig2, evX, hsv⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv x st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hsv; dsimp only at hsv
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      cases evRhs with
      | neg evRe hop =>
        have hveq := evalExprN_reifySVal_backward hsv evRe
        obtain ⟨hop', hr⟩ := evalNeg_valEq hveq hop
        exact ⟨_, hOrig2, .neg evX hop', ⟨_, hfind, hr⟩⟩
  | fuel, cur, dyn, senv, .binary op l r, st, locOpt, locOpt', locOrig, hOpt1, hOpt2, hOrig1, hc, hsc, hcalls, hsenv, henv, ev => by
    simp only [isCleanExpr, scopedExpr, Bool.and_eq_true] at hc hsc
    have hcallsL : ∀ nm, callsAny [nm] l = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAny, h])
    have hcallsR : ∀ nm, callsAny [nm] r = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAny, h])
    have hfnCleanMap : ∀ p ∈ fns.map fun f => (f.name, f), isCleanExpr p.2.body = true :=
      fun p hp => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hp; hfnClean p.2 hmem
    have hfnScopedMap : ∀ p ∈ fns.map fun f => (f.name, f), scopedExpr (p.2.params.map Prod.fst) p.2.body = true :=
      fun p hp => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hp; hfnScoped p.2 hmem
    rw [peExpr] at ev ⊢
    have hsyn1 := peExpr_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn senv l st hc.1 hsc.1 hsenv
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv l st with ⟨⟨b1, sv1⟩, st1⟩
    rw [h1] at hsyn1 ev ⊢; dsimp only at hsyn1 ev ⊢
    have hsyn2 := peExpr_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn senv r st1 hc.2 hsc.2 (hsenv.mono hsyn1.1)
    rcases h2 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv r st1 with ⟨⟨b2, sv2⟩, st2⟩
    rw [h2] at hsyn2 ev ⊢; dsimp only at hsyn2 ev ⊢
    have hboth : ∀ {locM2 : Environment F Nat} {hOptM2 : Heap F},
        EvalLetsN wOpt d locOpt (b1 ++ b2) hOpt1 locM2 hOptM2 →
        ∃ vL hOrigM vR hOrig2,
          EvalExpr wOrig [] locOrig (qualifyExprF F l) hOrig1 vL hOrigM ∧
          EvalExpr wOrig [] locOrig (qualifyExprF F r) hOrigM vR hOrig2 ∧
          SValDenotes hOptM2 hOrig2 locM2 sv1 vL ∧
          SValDenotes hOptM2 hOrig2 locM2 sv2 vR := by
      intro locM2 hOptM2 evBoth
      obtain ⟨locM1, hOptM1, evB1, evB2⟩ := evBoth.split_append
      obtain ⟨vL, hOrigM, evL, hsv1⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv l st hc.1 hsc.1 hcallsL hsenv henv (by rw [h1]; exact evB1)
      rw [h1] at hsv1; dsimp only at hsv1
      have henvM := EnvDenotes.lift evB1.heap_extends evL.heap_extends
        (evB1.preserves_notPEGe hsyn1.2.1) hsenv henv
      obtain ⟨vR, hOrig2, evR, hsv2⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv r st1 hc.2 hsc.2 hcallsR (hsenv.mono hsyn1.1) henvM (by rw [h2]; exact evB2)
      rw [h2] at hsv2; dsimp only at hsv2
      have hsv1' := SValDenotes.lift evB2.heap_extends evR.heap_extends
        (evB2.preserves_notPEGe hsyn2.2.1) hsyn1.2.2 hsv1
      exact ⟨vL, hOrigM, vR, hOrig2, evL, evR, hsv1', hsv2⟩
    have hfallback :
        EvalLetsN wOpt d locOpt (emitResidual (b1 ++ b2) (.binary op (reifySVal sv1) (reifySVal sv2)) st2).1.1
          hOpt1 locOpt' hOpt2 →
        ∃ vOrig hOrig2,
          EvalExpr wOrig [] locOrig (qualifyExprF F (.binary op l r)) hOrig1 vOrig hOrig2 ∧
          SValDenotes hOpt2 hOrig2 locOpt'
            (emitResidual (b1 ++ b2) (.binary op (reifySVal sv1) (reifySVal sv2)) st2).1.2 vOrig := by
      intro evF
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv evF
      obtain ⟨vL, hOrigM, vR, hOrig2, evL, evR, hsv1, hsv2⟩ := hboth evBs
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      cases evRhs with
      | binary evRe1 evRe2 hop =>
        have hveq1 := evalExprN_reifySVal_backward hsv1 evRe1
        have hsv2' := hsv2.mono_heaps evRe1.heap_extends (Heap.Extends.refl _)
        have hveq2 := evalExprN_reifySVal_backward hsv2' evRe2
        have hveq1' := hveq1.mono_heaps evRe2.heap_extends (Heap.Extends.refl _)
        obtain ⟨hop', hr⟩ := evalBinOp_valEq hveq1' hveq2 hop
        exact ⟨_, hOrig2, .binary evL evR hop', ⟨_, hfind, hr⟩⟩
    cases op with
    | add =>
      cases sv1 with
      | lit a =>
        cases sv2 with
        | lit b =>
          dsimp only at ev ⊢
          by_cases hcond : (a < natLimit && b < natLimit && a + b < natLimit) = true
          · simp only [hcond, ↓reduceIte] at ev ⊢
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨vL, hOrigM, vR, hOrig2, evL, evR, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ := hboth ev
            simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
            exact ⟨.field ((a + b : Nat) : F), hOrig2,
              .binary evL evR (by simp [evalBinOp, Nat.cast_add]), ⟨hcond.2, rfl⟩⟩
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev ⊢
            exact hfallback ev
        | _ => exact hfallback ev
      | _ => exact hfallback ev
    | sub =>
      cases sv1 with
      | lit a =>
        cases sv2 with
        | lit b =>
          dsimp only at ev ⊢
          by_cases hcond : (a < natLimit && b < natLimit) = true
          · simp only [hcond, ↓reduceIte] at ev ⊢
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            by_cases hle : b ≤ a
            · simp only [hle, ↓reduceIte] at ev ⊢
              obtain ⟨vL, hOrigM, vR, hOrig2, evL, evR, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ := hboth ev
              simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
              exact ⟨.field ((a - b : Nat) : F), hOrig2,
                .binary evL evR (by simp [evalBinOp, Nat.cast_sub hle]), ⟨by omega, rfl⟩⟩
            · simp only [hle, ↓reduceIte] at ev ⊢
              obtain ⟨vL, hOrigM, vR, hOrig2, evL, evR, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ := hboth ev
              simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
              exact ⟨.field ((a : F) - (b : F)), hOrig2,
                .binary evL evR (by simp [evalBinOp]), ⟨by omega, hcond.2, rfl⟩⟩
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev ⊢
            exact hfallback ev
        | _ => exact hfallback ev
      | _ => exact hfallback ev
    | mul =>
      cases sv1 with
      | lit a =>
        cases sv2 with
        | lit b =>
          dsimp only at ev ⊢
          by_cases hcond : (a < natLimit && b < natLimit && a * b < natLimit) = true
          · simp only [hcond, ↓reduceIte] at ev ⊢
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨vL, hOrigM, vR, hOrig2, evL, evR, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ := hboth ev
            simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
            exact ⟨.field ((a * b : Nat) : F), hOrig2,
              .binary evL evR (by simp [evalBinOp, Nat.cast_mul]), ⟨hcond.2, rfl⟩⟩
          · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev ⊢
            exact hfallback ev
        | _ => exact hfallback ev
      | _ => exact hfallback ev
    | div => exact hfallback ev
  | fuel, cur, dyn, senv, .builtin op xs, st, locOpt, locOpt', locOrig, hOpt1, hOpt2, hOrig1, hc, hsc, hcalls, hsenv, henv, ev => by
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bs, svs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    have hfallback :
        EvalLetsN wOpt d locOpt (emitResidual bs (.builtin op (reifySValList svs)) st1).1.1 hOpt1 locOpt' hOpt2 →
        ∃ vOrig hOrig2,
          EvalExpr wOrig [] locOrig (qualifyExprF F (.builtin op xs)) hOrig1 vOrig hOrig2 ∧
          SValDenotes hOpt2 hOrig2 locOpt' (emitResidual bs (.builtin op (reifySValList svs)) st1).1.2 vOrig := by
      intro evF
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv evF
      obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
        peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hvs; dsimp only at hvs
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      rw [map_qualifyExpr_map_cast] at evRhs ⊢
      cases evRhs with
      | builtin hargs ha =>
        have hveq := evalArgsN_reifySValList_backward hvs hargs
        obtain ⟨rOrig, ha', hr⟩ := builtin_apply_valEq hveq ha
        exact ⟨rOrig, hOrig2, .builtin evArgs ha', ⟨_, hfind, hr⟩⟩
    cases op with
    | assertEq msg =>
      cases svs with
      | cons sv1 rest1 =>
        cases sv1 with
        | lit a =>
          cases rest1 with
          | cons sv2 rest2 =>
            cases sv2 with
            | lit b =>
              cases rest2 with
              | nil =>
                dsimp only at ev ⊢
                by_cases hcond : (a == b && a < natLimit) = true
                · simp only [hcond, ↓reduceIte] at ev ⊢
                  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
                  obtain ⟨rfl, _⟩ := hcond
                  obtain ⟨vsOrig, hOrig2, evArgs, hvs⟩ :=
                    peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
                      fuel cur dyn senv xs st hc hsc hcalls hsenv henv (by rw [h1]; exact ev)
                  rw [h1] at hvs; dsimp only at hvs
                  cases vsOrig with
                  | nil => exact False.elim hvs
                  | cons v1 vs1 =>
                    cases vs1 with
                    | nil => exact False.elim hvs.2
                    | cons v2 vs2 =>
                      cases vs2 with
                      | cons _ _ => exact False.elim hvs.2.2
                      | nil =>
                        rcases hvs.1 with ⟨_, rfl⟩
                        rcases hvs.2.1 with ⟨_, rfl⟩
                        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
                        rw [map_qualifyExpr_map_cast]
                        exact ⟨.tuple [], hOrig2,
                          .builtin evArgs (by simp [Builtin.apply, evalAssertEq, Value.pointerFree]),
                          ⟨[], rfl, trivial⟩⟩
                · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev ⊢
                  exact hfallback ev
              | cons _ _ => exact hfallback ev
            | _ => exact hfallback ev
          | nil => exact hfallback ev
        | _ => exact hfallback ev
      | nil => exact hfallback ev
    | _ => exact hfallback ev
  | fuel, cur, dyn, senv, .letValue p rhs body, st, locOpt, locOpt', locOrig, hOpt1, hOpt2, hOrig1, hc, hsc, hcalls, hsenv, henv, ev => by
    simp only [isCleanExpr, scopedExpr, Bool.and_eq_true] at hc hsc
    have hcallsRhs : ∀ nm, callsAny [nm] rhs = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAny, h])
    have hcallsBody : ∀ nm, callsAny [nm] body = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAny, h])
    have hfnCleanMap : ∀ q ∈ fns.map fun f => (f.name, f), isCleanExpr q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnClean q.2 hmem
    have hfnScopedMap : ∀ q ∈ fns.map fun f => (f.name, f), scopedExpr (q.2.params.map Prod.fst) q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnScoped q.2 hmem
    rw [peExpr] at ev ⊢
    have hsyn1 := peExpr_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn senv rhs st hc.1.2 hsc.1 hsenv
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv rhs st with ⟨⟨bRhs, svRhs⟩, st1⟩
    rw [h1] at hsyn1 ev ⊢; dsimp only at hsyn1 ev ⊢
    cases hm : matchPatSVal p svRhs with
    | matched sbinds =>
      rw [hm] at ev; dsimp only at ev ⊢
      rcases h2 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn (sbinds ++ senv) body st1 with ⟨⟨bBody, svBody⟩, st2⟩
      dsimp only at ev ⊢
      obtain ⟨locM, hOptM, evRhs, evBody⟩ := ev.split_append
      obtain ⟨vRhs, hOrigM, evOrigRhs, hsvRhs⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv rhs st hc.1.2 hsc.1 hcallsRhs hsenv henv (by rw [h1]; exact evRhs)
      rw [h1] at hsvRhs; dsimp only at hsvRhs
      have hms := matchPatSVal_sound fc wOrig p svRhs vRhs hsvRhs
      rw [hm] at hms; dsimp only at hms
      obtain ⟨origBinds, hmOrig, hbd⟩ := hms
      have henvM := EnvDenotes.lift evRhs.heap_extends evOrigRhs.heap_extends
        (evRhs.preserves_notPEGe hsyn1.2.1) hsenv henv
      have ⟨hnb, hnames⟩ := matchPatSVal_notPEGe_aux p svRhs sbinds hsyn1.2.2 hm
      have hscB : scopedExpr ((sbinds ++ senv).map Prod.fst) body = true := by
        rw [List.map_append, hnames]; exact hsc.2
      obtain ⟨vBody, hOrig2, evOrigBody, hsvBody⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn (sbinds ++ senv) body st1 hc.2 hscB hcallsBody
          (hnb.append (hsenv.mono hsyn1.1)) (hbd.extend_env henvM) evBody
      rw [h2] at hsvBody; dsimp only at hsvBody
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
      exact ⟨vBody, hOrig2, .letValue evOrigRhs hmOrig evOrigBody, hsvBody⟩
    | noMatch | unknown =>
      rw [hm] at ev; dsimp only at ev ⊢
      have hfp := freshPat_props p st1 hc.1.1
      rcases hf : freshPat p st1 with ⟨⟨p', pBinds⟩, st2⟩
      rw [hf] at hfp; dsimp only at hfp ev ⊢
      rcases h2 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn (pBinds ++ senv) body st2 with ⟨⟨bBody, svBody⟩, st3⟩
      dsimp only at ev ⊢
      obtain ⟨locM1, hOptM1, evPre, evBody⟩ := ev.split_append
      obtain ⟨locM, hOptM, evRhs, evPat⟩ := evPre.split_append
      cases evPat with
      | cons evReify hmOpt evNil =>
        rename_i _ vOpt optBinds
        cases evNil
        obtain ⟨vRhs, hOrigM, evOrigRhs, hsvRhs⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv rhs st hc.1.2 hsc.1 hcallsRhs hsenv henv (by rw [h1]; exact evRhs)
        rw [h1] at hsvRhs; dsimp only at hsvRhs
        have hveq := evalExprN_reifySVal_backward hsvRhs evReify
        have hfm := freshPat_matchPattern_sound haux p st1 vOpt vRhs (some optBinds) hc.1.1 hveq hmOpt
        rw [hf] at hfm; dsimp only at hfm
        obtain ⟨origBinds, hmOrig, hrange, hbd_fn⟩ := hfm
        have hbd := hbd_fn (optBinds ++ locM) (fun _ _ _ _ hf' => find?_append_of_some hf')
        have hpres : ∀ y, NotPEGe st.nextId y →
            (optBinds ++ locM).find? (·.1 == y) = locOpt.find? (·.1 == y) := fun y hy => by
          rw [find?_append_skip_of_binds_inRange hrange (hy.mono hsyn1.1)]
          exact evRhs.preserves_notPEGe hsyn1.2.1 y hy
        have henvM := EnvDenotes.lift (evRhs.heap_extends.trans evReify.heap_extends)
          evOrigRhs.heap_extends hpres hsenv henv
        have hscB : scopedExpr ((pBinds ++ senv).map Prod.fst) body = true := by
          rw [List.map_append, hfp.2.2.2]; exact hsc.2
        rw [hf] at evBody; dsimp only at evBody
        obtain ⟨vBody, hOrig2, evOrigBody, hsvBody⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn (pBinds ++ senv) body st2 hc.2 hscB hcallsBody
            (hfp.2.2.1.append (hsenv.mono (Nat.le_trans hsyn1.1 hfp.1)))
            (hbd.extend_env henvM) evBody
        rw [h2] at hsvBody; dsimp only at hsvBody
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
        exact ⟨vBody, hOrig2, .letValue evOrigRhs hmOrig evOrigBody, hsvBody⟩
  | fuel, cur, dyn, senv, .matchValue scrut arms, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    simp only [isCleanExpr, scopedExpr, Bool.and_eq_true] at hc hsc
    have hcallsS : ∀ nm, callsAny [nm] scrut = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAny, h])
    have hcallsA : ∀ nm, callsAnyArms [nm] arms = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAny, h])
    have hfnCleanMap : ∀ q ∈ fns.map fun f => (f.name, f), isCleanExpr q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnClean q.2 hmem
    have hfnScopedMap : ∀ q ∈ fns.map fun f => (f.name, f), scopedExpr (q.2.params.map Prod.fst) q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnScoped q.2 hmem
    rw [peExpr.eq_def] at ev ⊢; dsimp only at ev ⊢
    have hsyn1 := peExpr_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn senv scrut st hc.1 hsc.1 hsenv
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv scrut st with ⟨⟨bScrut, svScrut⟩, st1⟩
    rw [h1] at hsyn1 ev ⊢; dsimp only at hsyn1 ev ⊢
    cases hsel : selectArmSVal svScrut arms with
    | some pair =>
      rcases pair with ⟨sbinds, armBody⟩
      rw [hsel] at ev; dsimp only at ev ⊢
      have _ : sizeOf armBody < sizeOf arms := PartialEval.selectArmSVal_sizeOf hsel
      rcases h2 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn (sbinds ++ senv) armBody st1 with ⟨⟨bArm, svArm⟩, st2⟩
      dsimp only at ev ⊢
      obtain ⟨locM, hOptM, evScrut, evArm⟩ := ev.split_append
      obtain ⟨vScrut, hOrigM, evOrigScrut, hsvScrut⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv scrut st hc.1 hsc.1 hcallsS hsenv henv (by rw [h1]; exact evScrut)
      rw [h1] at hsvScrut; dsimp only at hsvScrut
      obtain ⟨origBinds, hselOrig, hbd⟩ := selectArmSVal_sound fc wOrig hsvScrut hsel
      have ⟨hcArm, hnb, hscArm⟩ := selectArmSVal_clean_and_scoped hsyn1.2.2 hc.2 hsc.2 hsel
      have hscArm' : scopedExpr ((sbinds ++ senv).map Prod.fst) armBody = true := by
        rw [List.map_append]; exact hscArm
      obtain ⟨pArm, hmemArm⟩ := PartialEval.selectArmSVal_mem hsel
      have hcallsArm : ∀ nm, callsAny [nm] armBody = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
        fun nm h => hcallsA nm (callsAnyArms_of_mem hmemArm h)
      have henvM := EnvDenotes.lift evScrut.heap_extends evOrigScrut.heap_extends
        (evScrut.preserves_notPEGe hsyn1.2.1) hsenv henv
      obtain ⟨vArm, hOrig2, evOrigArm, hsvArm⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn (sbinds ++ senv) armBody st1 hcArm hscArm' hcallsArm
          (hnb.append (hsenv.mono hsyn1.1)) (hbd.extend_env henvM) evArm
      rw [h2] at hsvArm; dsimp only at hsvArm
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
      rw [map_qualifyArms]
      exact ⟨vArm, hOrig2, .matchValue evOrigScrut hselOrig evOrigArm, hsvArm⟩
    | none =>
      rw [hsel] at ev; dsimp only at ev ⊢
      obtain ⟨locM, hM, rOpt, evScrut, evMatch, hfind⟩ := evalLetsN_emitResidual_inv ev
      obtain ⟨vScrut, hOrigM, evOrigScrut, hsvScrut⟩ :=
        peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv scrut st hc.1 hsc.1 hcallsS hsenv henv (by rw [h1]; exact evScrut)
      rw [h1] at hsvScrut; dsimp only at hsvScrut
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evMatch ⊢
      rw [map_qualifyArms] at evMatch ⊢
      cases evMatch with
      | matchValue evReify hselOpt evArmOpt =>
        have hveqScrut := evalExprN_reifySVal_backward hsvScrut evReify
        have henvM := EnvDenotes.lift (evScrut.heap_extends.trans evReify.heap_extends)
          evOrigScrut.heap_extends (evScrut.preserves_notPEGe hsyn1.2.1) hsenv henv
        obtain ⟨origBinds, armBodyOrig, rOrig, hOrig2, hselOrig, evOrigArm, hrEq⟩ :=
          peArms_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur _ senv arms st1 hc.2 hsc.2 hcallsA (hsenv.mono hsyn1.1) henvM
            hveqScrut hselOpt evArmOpt
        exact ⟨rOrig, hOrig2, .matchValue evOrigScrut hselOrig evOrigArm, ⟨_, hfind, hrEq⟩⟩
  | fuel, cur, dyn, senv, .call nm targs xs, st, locOpt, locOpt', locOrig, hOpt1, hOpt2, hOrig1, hc, hsc, hcalls, hsenv, henv, ev => by
    have hcallsXs : ∀ m, callsAnyList [m] xs = true → ∃ f ∈ fns, callsAny [m] f.body = true :=
      fun m h => hcalls m (by simp [callsAny, h])
    rw [peExpr] at ev ⊢
    rcases h1 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st with ⟨⟨bArgs, svArgs⟩, st1⟩
    rw [h1] at ev ⊢; dsimp only at ev ⊢
    have hargs : ∀ {locM hOptM},
        EvalLetsN wOpt d locOpt bArgs hOpt1 locM hOptM →
        ∃ vsOrig hOrigM,
          EvalArgs wOrig [] locOrig (xs.map (qualifyExprF F)) hOrig1 vsOrig hOrigM ∧
          SValListDenotes hOptM hOrigM locM svArgs vsOrig := by
      intro locM hOptM evBs
      obtain ⟨vsOrig, hOrigM, evOrigArgs, hvs⟩ :=
        peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
          fuel cur dyn senv xs st hc hsc hcallsXs hsenv henv (by rw [h1]; exact evBs)
      rw [h1] at hvs; dsimp only at hvs
      exact ⟨vsOrig, hOrigM, evOrigArgs, hvs⟩
    have hfallback :
        EvalLetsN wOpt d locOpt (emitResidual bArgs (.call nm targs (reifySValList svArgs)) st1).1.1 hOpt1 locOpt' hOpt2 →
        ∃ vOrig hOrig2,
          EvalExpr wOrig [] locOrig (qualifyExprF F (.call nm targs xs)) hOrig1 vOrig hOrig2 ∧
          SValDenotes hOpt2 hOrig2 locOpt' (emitResidual bArgs (.call nm targs (reifySValList svArgs)) st1).1.2 vOrig := by
      intro evF
      obtain ⟨locM, hM, rOpt, evBs, evRhs, hfind⟩ := evalLetsN_emitResidual_inv evF
      obtain ⟨vsOrig, hOrigM, evOrigArgs, hvs⟩ := hargs evBs
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evRhs ⊢
      rw [map_qualifyExpr_map_cast] at evRhs ⊢
      cases evRhs with
      | call hlt hargsOpt hfnOpt =>
        have hveqArgs := evalArgsN_reifySValList_backward hvs hargsOpt
        obtain ⟨rOrig, hOrig2, evFnOrig, hrEq⟩ := hcall hlt hveqArgs hfnOpt
        exact ⟨rOrig, hOrig2, .call evOrigArgs evFnOrig, ⟨_, hfind, hrEq⟩⟩
    cases targs with
    | none => exact hfallback ev
    | some ts =>
      cases ts with
      | cons t ts => exact hfallback ev
      | nil =>
        dsimp only at ev ⊢
        cases hfold : tryFoldHelperCall nm svArgs with
        | some svRes =>
          rw [hfold] at ev; dsimp only at ev ⊢
          obtain ⟨vsOrig, hOrig2, evOrigArgs, hvs⟩ := hargs ev
          have hcalled : ∃ f ∈ fns, callsAny [nm] f.body = true :=
            hcalls nm (by simp [callsAny])
          obtain ⟨vRes, evFnOrig, hsvRes⟩ := tryFoldHelperCall_sound harith hcalled hvs hfold
          simp only [qualifyExprF, qualifyExpr, Option.map_some, List.map_nil, Aiur.Generic.Expr.map]
          rw [map_qualifyExpr_map_cast]
          exact ⟨vRes, hOrig2, .call evOrigArgs (by simpa [instanceName_nil] using evFnOrig), hsvRes⟩
        | none =>
          rw [hfold] at ev; dsimp only at ev ⊢
          cases fuel with
          | zero => exact hfallback ev
          | succ fuel' =>
            dsimp only at ev ⊢
            cases hcal : lookupEligibleCallee cfg (fns.map fun f => (f.name, f)) dyn nm svArgs st1.specSteps with
            | none =>
              rw [hcal] at ev; dsimp only at ev ⊢
              exact hfallback ev
            | some callee =>
              rw [hcal] at ev; dsimp only at ev ⊢
              have hspec := PartialEval.lookupEligibleCallee_spec hcal
              have hcalleeMem : callee ∈ fns := (mem_fns_of_mem_fnMap hspec.1).1
              have hcalleeArity : callee.params.length = svArgs.length := hspec.2.2
              have hcalleeNm : callee.name = nm := (mem_fns_of_mem_fnMap hspec.1).2
              have hfnCleanMap : ∀ q ∈ fns.map fun f => (f.name, f), isCleanExpr q.2.body = true :=
                fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnClean q.2 hmem
              have hfnScopedMap : ∀ q ∈ fns.map fun f => (f.name, f), scopedExpr (q.2.params.map Prod.fst) q.2.body = true :=
                fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnScoped q.2 hmem
              have hsyn1 := peExprList_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
                (fuel' + 1) cur dyn senv xs st hc hsc hsenv
              rw [h1] at hsyn1; dsimp only at hsyn1
              let st2 : PEState := { st1 with specSteps := st1.specSteps - 1 }
              let calleeSEnv : SEnv := (callee.params.map Prod.fst).zip svArgs
              rcases h2 : peExpr cfg (fns.map fun f => (f.name, f)) fuel' (some nm) dyn calleeSEnv callee.body st2 with
                ⟨⟨bCal, svRes⟩, st3⟩
              dsimp only [st2, calleeSEnv] at h2
              rw [h2] at ev ⊢; dsimp only at ev ⊢
              obtain ⟨locM, hOptM, evArgs, evCal⟩ := ev.split_append
              obtain ⟨vsOrig, hOrigM, evOrigArgs, hvs⟩ := hargs evArgs
              have hscCal : scopedExpr (calleeSEnv.map Prod.fst) callee.body = true := by
                dsimp only [calleeSEnv]
                rw [map_fst_zip_eq (by simp [hcalleeArity])]
                exact hfnScoped callee hcalleeMem
              have hcalSEnv : SEnvNotPEGe st2.nextId calleeSEnv := by
                intro q hq
                exact svalListNotPEGe_iff_forall.mp hsyn1.2.2 q.2 (List.of_mem_zip hq).2
              have hcallsCal : ∀ m, callsAny [m] callee.body = true → ∃ f ∈ fns, callsAny [m] f.body = true :=
                fun m h => ⟨callee, hcalleeMem, h⟩
              obtain ⟨vRes, hOrig2, evCalBody, hsvRes⟩ :=
                peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
                  fuel' (some nm) dyn calleeSEnv callee.body st2
                  (hfnClean callee hcalleeMem) hscCal hcallsCal hcalSEnv
                  (envDenotes_zip hvs) (by dsimp only [st2, calleeSEnv]; rw [h2]; exact evCal)
              dsimp only [st2, calleeSEnv] at hsvRes; rw [h2] at hsvRes; dsimp only at hsvRes
              have hlenOrig : vsOrig.length = (callee.params.map Prod.fst).length := by
                rw [List.length_map, ← svalListDenotes_length_eq hvs, hcalleeArity]
              have hprep := hOrigProv callee hcalleeMem vsOrig hlenOrig
              have hqnm : qualifyName nm = qualified callee.name := by
                rw [← hcalleeNm]
                exact qualifyName_of_noDoubleColon (hNoColon callee hcalleeMem)
              have evFnOrig : EvalFn wOrig (qualifyName nm) vsOrig hOrigM vRes hOrig2 := by
                rw [hqnm]
                exact EvalFn.intro hprep evCalBody
              simp only [qualifyExprF, qualifyExpr, Option.map_some, List.map_nil, Aiur.Generic.Expr.map]
              rw [map_qualifyExpr_map_cast]
              exact ⟨vRes, hOrig2, .call evOrigArgs (by simpa [instanceName_nil] using evFnOrig), hsvRes⟩
termination_by fuel _ _ _ e _ _ _ _ _ _ _ _ _ _ _ _ _ => (fuel, sizeOf e)

theorem peExprList_backward (fc : FieldCompatible64 F) (cfg : PEConfig) (fns : List Fn)
    {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (harith : Arith56WorldSpec fns wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (xs : List Expr) (st : PEState)
      {locOpt locOpt' locOrig : Environment F Nat} {hOpt1 hOpt2 hOrig1 : Heap F},
      isCleanList xs = true →
      scopedList (senv.map Prod.fst) xs = true →
      (∀ nm, callsAnyList [nm] xs = true → ∃ f ∈ fns, callsAny [nm] f.body = true) →
      SEnvNotPEGe st.nextId senv →
      EnvDenotes hOpt1 hOrig1 locOpt senv locOrig →
      EvalLetsN wOpt d locOpt
        (peExprList cfg (fns.map fun f => (f.name, f)) fuel curFn dynFns senv xs st).1.1
        hOpt1 locOpt' hOpt2 →
      ∃ vsOrig hOrig2,
        EvalArgs wOrig [] locOrig (xs.map (qualifyExprF F)) hOrig1 vsOrig hOrig2 ∧
        SValListDenotes hOpt2 hOrig2 locOpt'
          (peExprList cfg (fns.map fun f => (f.name, f)) fuel curFn dynFns senv xs st).1.2 vsOrig
  | _, _, _, _, [], st, _, _, _, _, _, _, _, _, _, _, _, ev => by
    rw [peExprList] at ev ⊢
    cases ev
    exact ⟨[], _, .nil, trivial⟩
  | fuel, cur, dyn, senv, x :: xs, st, _, _, _, _, _, _, hc, hsc, hcalls, hsenv, henv, ev => by
    simp only [isCleanList, scopedList, Bool.and_eq_true] at hc hsc
    have hcallsX : ∀ nm, callsAny [nm] x = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAnyList, h])
    have hcallsXs : ∀ nm, callsAnyList [nm] xs = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAnyList, h])
    have hfnCleanMap : ∀ q ∈ fns.map fun f => (f.name, f), isCleanExpr q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnClean q.2 hmem
    have hfnScopedMap : ∀ q ∈ fns.map fun f => (f.name, f), scopedExpr (q.2.params.map Prod.fst) q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnScoped q.2 hmem
    rw [peExprList] at ev ⊢
    have hsyn1 := peExpr_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn senv x st hc.1 hsc.1 hsenv
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv x st with ⟨⟨b1, sv1⟩, st1⟩
    rw [h1] at hsyn1 ev ⊢; dsimp only at hsyn1 ev ⊢
    have hsyn2 := peExprList_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn senv xs st1 hc.2 hsc.2 (hsenv.mono hsyn1.1)
    rcases h2 : peExprList cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv xs st1 with ⟨⟨b2, svs⟩, st2⟩
    rw [h2] at hsyn2 ev ⊢; dsimp only at hsyn2 ev ⊢
    obtain ⟨locM, hOptM, evB1, evB2⟩ := ev.split_append
    obtain ⟨vOrig, hOrigM, evX, hsv1⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv x st hc.1 hsc.1 hcallsX hsenv henv (by rw [h1]; exact evB1)
    rw [h1] at hsv1; dsimp only at hsv1
    have henvM := EnvDenotes.lift evB1.heap_extends evX.heap_extends
      (evB1.preserves_notPEGe hsyn1.2.1) hsenv henv
    obtain ⟨vsOrig, hOrig2, evXs, hvs⟩ :=
      peExprList_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        fuel cur dyn senv xs st1 hc.2 hsc.2 hcallsXs (hsenv.mono hsyn1.1) henvM (by rw [h2]; exact evB2)
    rw [h2] at hvs; dsimp only at hvs
    have hsv1' := SValDenotes.lift evB2.heap_extends evXs.heap_extends
      (evB2.preserves_notPEGe hsyn2.2.1) hsyn1.2.2 hsv1
    exact ⟨vOrig :: vsOrig, hOrig2, .cons evX evXs, ⟨hsv1', hvs⟩⟩
termination_by fuel _ _ _ xs _ _ _ _ _ _ _ _ _ _ _ _ _ => (fuel, sizeOf xs)

theorem peArms_backward (fc : FieldCompatible64 F) (cfg : PEConfig) (fns : List Fn)
    {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (harith : Arith56WorldSpec fns wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig) :
    ∀ (fuel : Nat) (curFn : Option String) (dynFns : List String)
      (senv : SEnv) (arms : List (Pat × Expr)) (st : PEState)
      {locOpt locOrig : Environment F Nat} {hOpt1 hOpt2 hOrig1 : Heap F}
      {vOpt vOrig rOpt : SourceValue F} {optBinds : Environment F Nat}
      {armBodyOpt : Aiur.Generic.Expr F},
      isCleanArms arms = true →
      scopedArms (senv.map Prod.fst) arms = true →
      (∀ nm, callsAnyArms [nm] arms = true → ∃ f ∈ fns, callsAny [nm] f.body = true) →
      SEnvNotPEGe st.nextId senv →
      EnvDenotes hOpt1 hOrig1 locOpt senv locOrig →
      ValEq hOpt1 hOrig1 hOpt1.length vOpt vOrig →
      SourceSemantics.selectArm wOpt [] hOpt1 vOpt
        ((peArms cfg (fns.map fun f => (f.name, f)) fuel curFn dynFns senv arms st).1.map
          fun (p, b) => (qualifyPatF F p, qualifyExprF F b)) = .ok (some (optBinds, armBodyOpt)) →
      EvalExprN wOpt d [] (optBinds ++ locOpt) armBodyOpt hOpt1 rOpt hOpt2 →
      ∃ origBinds armBodyOrig rOrig hOrig2,
        SourceSemantics.selectArm wOrig [] hOrig1 vOrig
          (arms.map fun (p, b) => (qualifyPatF F p, qualifyExprF F b)) =
          .ok (some (origBinds, armBodyOrig)) ∧
        EvalExpr wOrig [] (origBinds ++ locOrig) armBodyOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig
  | _, _, _, _, [], st, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsel, _ => by
    rw [peArms] at hsel; simp [SourceSemantics.selectArm] at hsel
  | fuel, cur, dyn, senv, (p, b) :: rest, st, locOpt, locOrig, hOpt1, hOpt2, hOrig1, vOpt, vOrig, rOpt, optBinds, armBodyOpt,
      hc, hsc, hcalls, hsenv, henv, hv, hsel, evArm => by
    simp only [isCleanArms, scopedArms, Bool.and_eq_true] at hc hsc
    have hcallsB : ∀ nm, callsAny [nm] b = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAnyArms, h])
    have hcallsRest : ∀ nm, callsAnyArms [nm] rest = true → ∃ f ∈ fns, callsAny [nm] f.body = true :=
      fun nm h => hcalls nm (by simp [callsAnyArms, h])
    have hfnCleanMap : ∀ q ∈ fns.map fun f => (f.name, f), isCleanExpr q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnClean q.2 hmem
    have hfnScopedMap : ∀ q ∈ fns.map fun f => (f.name, f), scopedExpr (q.2.params.map Prod.fst) q.2.body = true :=
      fun q hq => let ⟨hmem, _⟩ := mem_fns_of_mem_fnMap hq; hfnScoped q.2 hmem
    rw [peArms] at hsel
    have hfp := freshPat_props p st hc.1.1
    rcases hf : freshPat p st with ⟨⟨p', pBinds⟩, st1⟩
    rw [hf] at hfp hsel; dsimp only at hfp hsel
    have hscB : scopedExpr ((pBinds ++ senv).map Prod.fst) b = true := by
      rw [List.map_append, hfp.2.2.2]; exact hsc.1
    have hsynB := peExpr_syntax_props cfg (fns.map fun f => (f.name, f)) hfnCleanMap hfnScopedMap
      fuel cur dyn (pBinds ++ senv) b st1 hc.1.2 hscB (hfp.2.2.1.append (hsenv.mono hfp.1))
    rcases h1 : peExpr cfg (fns.map fun f => (f.name, f)) fuel cur dyn (pBinds ++ senv) b st1 with ⟨⟨bArm, svArm⟩, st2⟩
    rw [h1] at hsynB hsel; dsimp only at hsynB hsel
    rcases h2 : peArms cfg (fns.map fun f => (f.name, f)) fuel cur dyn senv rest st2 with ⟨rest', st3⟩
    rw [h2] at hsel; dsimp only at hsel
    simp only [List.map_cons, SourceSemantics.selectArm] at hsel ⊢
    cases hm : wOpt.matchPattern [] hOpt1 (qualifyPatF F p') vOpt with
    | error e => simp [hm, bind, Except.bind] at hsel
    | ok optM =>
      simp only [hm, bind, Except.bind] at hsel
      cases optM with
      | some ob1 =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        have hfm := freshPat_matchPattern_sound haux p st vOpt vOrig (some ob1) hc.1.1 hv (by rw [hf]; exact hm)
        rw [hf] at hfm; dsimp only at hfm
        obtain ⟨origBinds, hmOrig, hrange, hbd_fn⟩ := hfm
        have hbd := hbd_fn (ob1 ++ locOpt) (fun _ _ _ _ hf' => find?_append_of_some hf')
        have henvExt := EnvDenotes.lift (Heap.Extends.refl _) (Heap.Extends.refl _)
          (fun y hy => find?_append_skip_of_binds_inRange hrange hy) hsenv henv
        obtain ⟨loc2, hOptM, evLets, evReify⟩ := evalExprN_wrapLetsTail_inv evArm
        obtain ⟨rOrig, hOrig2, evOrigB, hsvArm⟩ :=
          peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn (pBinds ++ senv) b st1 hc.1.2 hscB hcallsB
            (hfp.2.2.1.append (hsenv.mono hfp.1)) (hbd.extend_env henvExt) (by rw [h1]; exact evLets)
        rw [h1] at hsvArm; dsimp only at hsvArm
        have hrEq := evalExprN_reifySVal_backward hsvArm evReify
        exact ⟨origBinds, qualifyExprF F b, rOrig, hOrig2,
          by simp [hmOrig, bind, Except.bind], evOrigB, hrEq⟩
      | none =>
        have hmOrig := freshPat_matchPattern_sound haux p st vOpt vOrig none hc.1.1 hv (by rw [hf]; exact hm)
        obtain ⟨origBinds, armBodyOrig, rOrig, hOrig2, hselRest, evOrigArm, hrEq⟩ :=
          peArms_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
            fuel cur dyn senv rest st2 hc.2 hsc.2 hcallsRest
            (hsenv.mono (Nat.le_trans hfp.1 hsynB.1)) henv hv (by rw [h2]; exact hsel) evArm
        exact ⟨origBinds, armBodyOrig, rOrig, hOrig2,
          by simp [hmOrig, hselRest, bind, Except.bind], evOrigArm, hrEq⟩
termination_by fuel _ _ _ arms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => (fuel, sizeOf arms)

end

/-! ### Function-Level & Program-Level Backward Simulation -/

theorem peFn_backward (fc : FieldCompatible64 F) (cfg : PEConfig) (fns : List Fn)
    {wOpt wOrig : World F} {d : Nat}
    (haux : SameAuxWorld wOpt wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hOptHas : WorldHasFns wOpt (partialEvalFns cfg fns))
    (hOrigProv : WorldProvidesFns wOrig fns)
    (harith : Arith56WorldSpec fns wOrig)
    (hcall : ∀ {d' : Nat} {nm : String} {vsOpt vsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      d' < d →
      ValEqList hOpt1 hOrig1 hOpt1.length vsOpt vsOrig →
      EvalFnN wOpt d' nm vsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm vsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig)
    {f : Fn} (hf : f ∈ fns)
    {argsOpt argsOrig : List (SourceValue F)} {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F}
    (hargs : ValEqList hOpt1 hOrig1 hOpt1.length argsOpt argsOrig)
    (ev : EvalFnN wOpt d (qualified f.name) argsOpt hOpt1 rOpt hOpt2) :
    ∃ rOrig hOrig2,
      EvalFn wOrig (qualified f.name) argsOrig hOrig1 rOrig hOrig2 ∧
      ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig := by
  let fnMap := fns.map fun g => (g.name, g)
  have hfOptMem : peFn cfg fnMap f ∈ partialEvalFns cfg fns :=
    List.mem_map.mpr ⟨f, hf, rfl⟩
  have hfnHas : WorldHasFn wOpt (qualified f.name) (f.params.map Prod.fst)
      (qualifyExprF F (peFn cfg fnMap f).body) := by
    have := hOptHas (peFn cfg fnMap f) hfOptMem
    rwa [peFn_name, peFn_params] at this
  have hplainFns : ∀ g ∈ fns, isPlainExpr g.body = true :=
    fun g hg => isCleanExpr_imp_isPlainExpr g.body (hfnClean g hg)
  have hplainOpt : isPlainExpr (qualifyExprF F (peFn cfg fnMap f).body) = true := by
    rw [isPlainExpr_qualifyExprF]
    exact PartialEval.isPlainExpr_partialEvalFns cfg hplainFns (peFn cfg fnMap f) hfOptMem
  obtain ⟨hlenOpt, evBody⟩ := Backward.evalFnN_plain_inv hfnHas hplainOpt ev
  have hlenOrig : argsOrig.length = (f.params.map Prod.fst).length := by
    rw [← hargs.length_eq, hlenOpt]
  have hprepOrig := hOrigProv f hf argsOrig hlenOrig
  unfold peFn at evBody
  by_cases hskip : (!f.typeParams.isEmpty || cfg.noSpecFns.contains f.name ||
      (f.params.map Prod.fst).any hasPEPrefix) = true
  · simp only [hskip, ↓reduceIte] at evBody
    have henvEq := EnvValEq.zip (ks := f.params.map Prod.fst) hargs
    obtain ⟨rOrig, hOrig2, evOrigBody, hrEq⟩ :=
      evalExprN_valEq_transfer haux hcall henvEq evBody
    exact ⟨rOrig, hOrig2, EvalFn.intro hprepOrig evOrigBody, hrEq⟩
  · simp only [hskip, Bool.false_eq_true, ↓reduceIte] at evBody
    have hnoPref : ∀ p ∈ f.params.map Prod.fst, hasPEPrefix p = false := by
      intro p hp
      cases hpf : hasPEPrefix p with
      | false => rfl
      | true =>
        have hany : (f.params.map Prod.fst).any hasPEPrefix = true :=
          List.any_eq_true.mpr ⟨p, hp, hpf⟩
        simp [hany] at hskip
    let initSEnv : SEnv := f.params.map fun (p, _) => (p, SVal.var p)
    have hinitSEnv_eq : initSEnv = (f.params.map Prod.fst).map fun p => (p, SVal.var p) := by
      simp [initSEnv, List.map_map, Function.comp_def]
    have hinitMapFst : initSEnv.map Prod.fst = f.params.map Prod.fst := by
      rw [hinitSEnv_eq, List.map_map]; simp [Function.comp_def]
    have hinitNotPE : SEnvNotPEGe 0 initSEnv := by
      intro q hq
      rw [hinitSEnv_eq] at hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      exact notPEGe_of_not_hasPEPrefix (hnoPref p hp)
    have hinitDen : EnvDenotes hOpt1 hOrig1 ((f.params.map Prod.fst).zip argsOpt)
        initSEnv ((f.params.map Prod.fst).zip argsOrig) := by
      rw [hinitSEnv_eq]
      exact envDenotes_init hargs hlenOpt.symm
    have hscF : scopedExpr (initSEnv.map Prod.fst) f.body = true := by
      rw [hinitMapFst]; exact hfnScoped f hf
    have hcallsF : ∀ nm, callsAny [nm] f.body = true → ∃ g ∈ fns, callsAny [nm] g.body = true :=
      fun nm h => ⟨f, hf, h⟩
    rcases hpe : peExpr cfg fnMap cfg.maxSpecDepth (some f.name) [] initSEnv f.body
        { nextId := 0, specSteps := cfg.maxSpecSteps } with ⟨⟨binds, sv⟩, stEnd⟩
    rw [hpe] at evBody; dsimp only at evBody
    obtain ⟨loc1, hOptM, evLets, evReify⟩ := evalExprN_wrapLetsTail_inv evBody
    obtain ⟨rOrig, hOrig2, evOrigBody, hsv⟩ :=
      peExpr_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOrigProv harith hcall
        cfg.maxSpecDepth (some f.name) [] initSEnv f.body
        { nextId := 0, specSteps := cfg.maxSpecSteps }
        (hfnClean f hf) hscF hcallsF hinitNotPE hinitDen (by rw [hpe]; exact evLets)
    rw [hpe] at hsv; dsimp only at hsv
    have hrEq := evalExprN_reifySVal_backward hsv evReify
    exact ⟨rOrig, hOrig2, EvalFn.intro hprepOrig evOrigBody, hrEq⟩

/-- Depth-indexed backward simulation for `partialEvalFns` by strong induction on call depth `d`. -/
theorem partialEvalFns_evalFnN_backward (fc : FieldCompatible64 F) (cfg : PEConfig) (fns : List Fn)
    {wOpt wOrig : World F}
    (haux : SameAuxWorld wOpt wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hOptHas : WorldHasFns wOpt (partialEvalFns cfg fns))
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : PrepareSameOnNonProg wOpt wOrig)
    (hClosed : PrepareClosedOnProg wOpt wOrig (partialEvalFns cfg fns))
    (harith : Arith56WorldSpec fns wOrig) :
    ∀ (d : Nat) {nm : String} {argsOpt argsOrig : List (SourceValue F)}
      {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F},
      ValEqList hOpt1 hOrig1 hOpt1.length argsOpt argsOrig →
      EvalFnN wOpt d nm argsOpt hOpt1 rOpt hOpt2 →
      ∃ rOrig hOrig2,
        EvalFn wOrig nm argsOrig hOrig1 rOrig hOrig2 ∧
        ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro nm argsOpt argsOrig hOpt1 hOpt2 hOrig1 rOpt hargs ev
    have hcall : ∀ {d' : Nat} {m : String} {vsOpt vsOrig : List (SourceValue F)}
        {ha1 ha2 hb1 : Heap F} {ro : SourceValue F},
        d' < d →
        ValEqList ha1 hb1 ha1.length vsOpt vsOrig →
        EvalFnN wOpt d' m vsOpt ha1 ro ha2 →
        ∃ rOrig hb2,
          EvalFn wOrig m vsOrig hb1 rOrig hb2 ∧
          ValEq ha2 hb2 ha2.length ro rOrig :=
      fun hlt hvs hev => ih _ hlt hvs hev
    by_cases hmem : ∃ f ∈ fns, qualified f.name = nm
    · obtain ⟨f, hf, rfl⟩ := hmem
      exact peFn_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOptHas hOrigProv harith
        hcall hf hargs ev
    · have hnotOpt : ∀ g ∈ partialEvalFns cfg fns, qualified g.name ≠ nm := by
        intro g hg heq
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
        rw [peFn_name] at heq
        exact hmem ⟨f, hf, heq⟩
      have hprepSame : ∀ types loc1 body,
          wOpt.prepare nm argsOpt = .ok (types, loc1, body) →
          ∃ pnames : List String, loc1 = pnames.zip argsOpt ∧
            wOrig.prepare nm argsOrig = .ok (types, pnames.zip argsOrig, body) := by
        intro types loc1 body hp
        cases hnp : isProgQName nm with
        | false => exact hNonProg nm argsOpt argsOrig types loc1 body hnp hargs.length_eq hp
        | true => exact hClosed nm argsOpt argsOrig types loc1 body hnp hnotOpt hargs.length_eq hp
      cases ev with
      | intro prep bodyEv =>
        obtain ⟨pnames, rfl, prepOrig⟩ := hprepSame _ _ _ prep
        obtain ⟨rOrig, hOrig2, evOrig, hrEq⟩ :=
          evalExprN_valEq_transfer haux hcall (EnvValEq.zip hargs) bodyEv
        exact ⟨rOrig, hOrig2, EvalFn.intro prepOrig evOrig, hrEq⟩
      | returned prep exitEv =>
        obtain ⟨pnames, rfl, prepOrig⟩ := hprepSame _ _ _ prep
        obtain ⟨rOrig, hOrig2, evOrig, hrEq⟩ :=
          evalExitN_valEq_transfer haux hcall (EnvValEq.zip hargs) exitEv
        exact ⟨rOrig, hOrig2, EvalFn.returned prepOrig evOrig, hrEq⟩

/-- Full backward `EvalFn` simulation for `partialEvalFns`: any execution in a world
implementing `partialEvalFns cfg fns` simulates back to `wOrig` with `ValEq` output. -/
theorem partialEvalFns_backward (fc : FieldCompatible64 F) (cfg : PEConfig) (fns : List Fn)
    {wOpt wOrig : World F}
    (haux : SameAuxWorld wOpt wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hOptHas : WorldHasFns wOpt (partialEvalFns cfg fns))
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : PrepareSameOnNonProg wOpt wOrig)
    (hClosed : PrepareClosedOnProg wOpt wOrig (partialEvalFns cfg fns))
    (harith : Arith56WorldSpec fns wOrig)
    {nm : String} {argsOpt argsOrig : List (SourceValue F)}
    {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F}
    (hargs : ValEqList hOpt1 hOrig1 hOpt1.length argsOpt argsOrig)
    (ev : EvalFn wOpt nm argsOpt hOpt1 rOpt hOpt2) :
    ∃ rOrig hOrig2,
      EvalFn wOrig nm argsOrig hOrig1 rOrig hOrig2 ∧
      ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig := by
  obtain ⟨d, evN⟩ := Backward.EvalFnN.ofEvalFn ev
  exact partialEvalFns_evalFnN_backward fc cfg fns haux hfnClean hfnScoped hNoColon hOptHas
    hOrigProv hNonProg hClosed harith d hargs evN

/-- End-to-end backward `EvalFn` simulation for `partialEvalFnsPruned` (combining partial
evaluation, specialization, constant folding, and `pruneUnreachable`). -/
theorem partialEvalFnsPruned_backward (fc : FieldCompatible64 F) (cfg : PEConfig)
    (roots : List String) (fns : List Fn)
    {wPruned wOrig : World F}
    (hNodup : (fns.map (·.name)).Nodup)
    (haux : SameAuxWorld wPruned wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hPrunedHas : WorldHasFns wPruned (partialEvalFnsPruned cfg roots fns))
    (hOnlyKept : ∀ f ∈ partialEvalFns cfg fns, f ∉ partialEvalFnsPruned cfg roots fns →
      ∀ args res, wPruned.prepare (qualified f.name) args ≠ .ok res)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : PrepareSameOnNonProg wPruned wOrig)
    (hClosed : PrepareClosedOnProg wPruned wOrig (partialEvalFnsPruned cfg roots fns))
    (harith : Arith56WorldSpec fns wOrig)
    {nm : String} {argsOpt argsOrig : List (SourceValue F)}
    {hOpt1 hOpt2 hOrig1 : Heap F} {rOpt : SourceValue F}
    (hargs : ValEqList hOpt1 hOrig1 hOpt1.length argsOpt argsOrig)
    (ev : EvalFn wPruned nm argsOpt hOpt1 rOpt hOpt2) :
    ∃ rOrig hOrig2,
      EvalFn wOrig nm argsOrig hOrig1 rOrig hOrig2 ∧
      ValEq hOpt2 hOrig2 hOpt2.length rOpt rOrig := by
  unfold partialEvalFnsPruned at hPrunedHas hOnlyKept hClosed
  cases hprune : cfg.prune with
  | false =>
    simp only [hprune, Bool.false_eq_true, ↓reduceIte] at hPrunedHas hClosed
    exact partialEvalFns_backward fc cfg fns haux hfnClean hfnScoped hNoColon
      hPrunedHas hOrigProv hNonProg hClosed harith hargs ev
  | true =>
    simp only [hprune, ↓reduceIte] at hPrunedHas hOnlyKept hClosed
    let optFns := partialEvalFns cfg fns
    let wOverlay := overlayWorld wPruned optFns
    have evOverlay : EvalFn wOverlay nm argsOpt hOpt1 rOpt hOpt2 :=
      pruneUnreachable_overlay_backward hPrunedHas hOnlyKept ev
    have hNodupOpt : (optFns.map (·.name)).Nodup := by
      dsimp only [optFns]; rw [partialEvalFns_map_name]; exact hNodup
    have hauxOverlay : SameAuxWorld wOverlay wOrig :=
      (sameAuxWorld_overlayWorld wPruned optFns).trans haux
    have hHasOverlay : WorldHasFns wOverlay optFns :=
      overlayWorld_hasFns wPruned hNodupOpt
    have hNonProgOverlay : PrepareSameOnNonProg wOverlay wOrig := by
      intro m a1 a2 types loc1 body hnp hlen hp
      rw [overlayWorld_prepare_nonProg wPruned optFns hnp] at hp
      exact hNonProg m a1 a2 types loc1 body hnp hlen hp
    have hClosedOverlay : PrepareClosedOnProg wOverlay wOrig optFns := by
      intro m a1 a2 types loc1 body hp hnotOpt hlen hprep
      have hfindNone : optFns.find? (fun f => qualified f.name == m) = none := by
        rw [List.find?_eq_none]
        intro f hf hbeq
        exact hnotOpt f hf (beq_iff_eq.mp hbeq)
      unfold wOverlay overlayWorld at hprep
      dsimp only at hprep
      rw [hfindNone] at hprep
      have hnotPruned : ∀ f ∈ pruneUnreachable roots optFns, qualified f.name ≠ m := by
        intro f hf
        exact hnotOpt f (List.mem_filter.mp hf).1
      exact hClosed m a1 a2 types loc1 body hp hnotPruned hlen hprep
    exact partialEvalFns_backward fc cfg fns hauxOverlay hfnClean hfnScoped hNoColon
      hHasOverlay hOrigProv hNonProgOverlay hClosedOverlay harith hargs evOverlay

/-- Entrypoint backward soundness theorem for `partialEvalProg` / `partialEvalFnsPruned`:
for pointer-free entry arguments `args` and pointer-free output `r`, any execution of the
partially evaluated + pruned program yields an execution of the original program with the
**exact identical result `r`** (starting from empty heap `[]`). -/
theorem partialEval_entry_backward (fc : FieldCompatible64 F) (cfg : PEConfig)
    (roots : List String) (fns : List Fn)
    {wPruned wOrig : World F}
    (hNodup : (fns.map (·.name)).Nodup)
    (haux : SameAuxWorld wPruned wOrig)
    (hfnClean : ∀ f ∈ fns, isCleanExpr f.body = true)
    (hfnScoped : ∀ f ∈ fns, scopedExpr (f.params.map Prod.fst) f.body = true)
    (hNoColon : ∀ f ∈ fns, hasDoubleColon f.name.toList = false)
    (hPrunedHas : WorldHasFns wPruned (partialEvalFnsPruned cfg roots fns))
    (hOnlyKept : ∀ f ∈ partialEvalFns cfg fns, f ∉ partialEvalFnsPruned cfg roots fns →
      ∀ args res, wPruned.prepare (qualified f.name) args ≠ .ok res)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : PrepareSameOnNonProg wPruned wOrig)
    (hClosed : PrepareClosedOnProg wPruned wOrig (partialEvalFnsPruned cfg roots fns))
    (harith : Arith56WorldSpec fns wOrig)
    {entry : String} {args : List (SourceValue F)} {r : SourceValue F} {hOpt' : Heap F}
    (hargsPf : ∀ a ∈ args, a.pointerFree = true)
    (hrPf : r.pointerFree = true)
    (ev : EvalFn wPruned (qualified entry) args [] r hOpt') :
    ∃ hOrig', EvalFn wOrig (qualified entry) args [] r hOrig' := by
  have hargsEq : ValEqList ([] : Heap F) ([] : Heap F) ([] : Heap F).length args args := by
    clear ev
    rw [valEqList_iff_forall₂]
    induction args with
    | nil => exact .nil
    | cons a as ih =>
      exact .cons (ValEq.refl_of_pointerFree (hargsPf a List.mem_cons_self))
        (ih (fun x hx => hargsPf x (List.mem_cons_of_mem _ hx)))
  obtain ⟨rOrig, hOrig', evOrig, hrEq⟩ :=
    partialEvalFnsPruned_backward fc cfg roots fns hNodup haux hfnClean hfnScoped hNoColon
      hPrunedHas hOnlyKept hOrigProv hNonProg hClosed harith hargsEq ev
  have hrId : r = rOrig := ValEq.eq_of_pointerFree hrPf hrEq
  subst hrId
  exact ⟨hOrig', evOrig⟩

end BackwardSim

/-! ## Section 7: Axiom Audit -/

/-- info: 'IxCC.AiurBackend.PartialEvalProof.partialEvalFns_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms partialEvalFns_backward

/--
info: 'IxCC.AiurBackend.PartialEvalProof.partialEvalFnsPruned_backward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms partialEvalFnsPruned_backward

/--
info: 'IxCC.AiurBackend.PartialEvalProof.partialEval_entry_backward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms partialEval_entry_backward

/-- info: 'IxCC.AiurBackend.PartialEvalProof.arith56WorldSpec_of_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arith56WorldSpec_of_world

/-- info: 'IxCC.AiurBackend.PartialEval.isPlainExpr_partialEvalProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PartialEval.isPlainExpr_partialEvalProg

end IxCC.AiurBackend.PartialEvalProof
