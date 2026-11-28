import IxCCAiur.InlineFuse
import IxCCAiur.TypedGadgets
import IxCCAiur.Backward

/-! # Certified Backward Simulation for `IxCCAiur.InlineFuse`

Proves complete, end-to-end backward simulation from
`Aiur.Generic.SourceSemantics.{EvalExpr, EvalFn}` on programs optimized by
`IxCC.AiurBackend.InlineFuse.optimizeFns` + `pruneUnreachable` back to the
unoptimized `TypedLower` program:

1. **World infrastructure & `pruneUnreachable` soundness** (`evalFn_of_worldSub`,
   `overlayWorld`, `pruneUnreachable_backward`, `world_transformBodies_backward`).
2. **Clean expressions, free/bound variables & local-environment congruence**
   (`isSimplePat`, `isCleanExpr`, `matchPattern_names_of_simple`,
   `evalExpr_localsAgree`).
3. **Sound `UInt32` value typing (`ValOk`, `HasTy`, `U32WorldSpec`)**:
   automatically establishes `Peephole.isU32Val` for every `UInt32::U32`-typed
   value and variable from program well-typedness (`evalExpr_valOk`), together
   with constructive bridge theorems (`evalFn_u32_of_field_mk`,
   `evalFn_compact_field_mk`, `evalFn_compact_mk`, `evalFn_from_fields_mk`,
   `evalFn_from_field_mk`) and `world_transformBodies_typed_backward`.
4. **`foldConstU32OfField` backward soundness** (`evalExpr_foldConstU32OfField_backward`).
5. **`Peephole.rewriteExpr` full `UInt32` backward soundness**
   (`evalExpr_lowerByteShifts_backward`, `evalExpr_fuseExpr_backward`,
   `evalExpr_peephole_backward`), composing directly with `Peephole.lean`'s
   proved `EvalExpr` soundness theorems.
6. **`flattenLets` backward soundness** (`evalExpr_flattenLets_backward`).
7. **`inlineCallsM` & `prefixExpr` alpha-renaming backward soundness**
   (`evalExpr_prefixExpr_backward`, `evalExpr_inlineCallsM_backward`).
8. **`simpExpr` backward soundness** (`evalExpr_simpExpr_backward`): covers
   copy propagation, known-constructor `matchValue` folding, dead pure `let`
   elimination, eta-reduction, and `u32_of_field`/`UInt32::from_field`
   round-trip cancellation (`compact_field (compact x)`).
9. **Top-level composition** (`inlineAndFoldOnce_backward`,
   `optimizeFns_backward`, `inlineFuse_backward`, `inlineFuse_entry_backward`).

Strictly zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`,
zero `bv_decide`, zero `partial`, zero `unsafe`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.InlineFuseProof

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower
  (Expr Pat Fn natLimit moduleName qualified qualifyName qualifyTy qualifyPat
   qualifyExpr qualifyPatF qualifyExprF hasDoubleColon allDistinct allDistinct_iff_nodup
   isPlainExpr isPlainList isPlainArms isPlainExpr_qualifyExprF)
open IxCC.AiurBackend.Gadgets
  (WorldHasFn no_evalExit_of_plain evalFn_plain_inv
   evalExpr_literal_inv evalExpr_var_inv evalExpr_binary_inv evalExpr_index_inv
   evalExpr_call_inv evalExpr_call1_inv evalExpr_call2_inv evalExpr_tuple2_inv
   evalExpr_let_wildcard_inv evalExpr_let_bind_inv evalExpr_let_tuple2_inv
   evalExpr_let_tuple2_wild_inv)
open IxCC.AiurBackend.TypedRep (u8Ty u32Ty u64Ty)
open IxCC.AiurBackend.TypedLower (u32OfFieldFn)
open IxCC.AiurBackend.TypedGadgets (FieldCompatible64 evalExpr_call3_inv evalExpr_array4_inv)
open IxCC.AiurBackend.Backward (EvalExprN EvalArgsN EvalFnN EvalExitN EvalArgsExitN)
open IxCC.AiurBackend.Peephole (isU32Val isU32Val_lt isU32Val_unique isU32Val_val_unique)
open IxCC.AiurBackend.InlineFuse

/-! ## Section 1: World Infrastructure, World Transfer & `pruneUnreachable` Soundness -/

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
  | _, _, _, _, _, _, .repeat v => .repeat (evalExpr_of_worldSub hsub v)
  | _, _, _, _, _, _, .index v hp => .index (evalExpr_of_worldSub hsub v) hp
  | _, _, _, _, _, _, .slice v hs => .slice (evalExpr_of_worldSub hsub v) hs
  | _, _, _, _, _, _, .builtin xs ha => .builtin (evalArgs_of_worldSub hsub xs) ha
  | _, _, _, _, _, _, .update xs ha => .update (evalArgs_of_worldSub hsub xs) ha
  | _, _, _, _, _, _, .record xs => .record (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .member v hp => .member (evalExpr_of_worldSub hsub v) hp
  | _, _, _, _, _, _, .construct xs => .construct (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .constructAs xs => .constructAs (evalArgs_of_worldSub hsub xs)
  | _, _, _, _, _, _, .project v hp => .project (evalExpr_of_worldSub hsub v) hp
  | _, _, _, _, _, _, .letValue v hm b =>
    .letValue (evalExpr_of_worldSub hsub v)
      (by rw [← hsub.aux.matchPattern_eq]; exact hm) (evalExpr_of_worldSub hsub b)
  | _, _, _, _, _, _, .store v => .store (evalExpr_of_worldSub hsub v)
  | _, _, _, _, _, _, .load v hl => .load (evalExpr_of_worldSub hsub v) hl
  | _, _, _, _, _, _, .hint k ht =>
    .hint (evalExpr_of_worldSub hsub k) (by rw [← hsub.aux.typed_eq]; exact ht)
  | _, _, _, _, _, _, .neg v hop => .neg (evalExpr_of_worldSub hsub v) hop
  | _, _, _, _, _, _, .binary l r hop =>
    .binary (evalExpr_of_worldSub hsub l) (evalExpr_of_worldSub hsub r) hop
  | _, _, _, _, _, _, .call xs cal =>
    .call (evalArgs_of_worldSub hsub xs) (evalFn_of_worldSub hsub cal)
  | _, _, _, _, _, _, .matchValue v hs b =>
    .matchValue (evalExpr_of_worldSub hsub v)
      (by rw [← hsub.aux.selectArm_eq]; exact hs) (evalExpr_of_worldSub hsub b)

theorem evalArgs_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs w1 types locals es h vs h' → EvalArgs w2 types locals es h vs h'
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons hd tl =>
    .cons (evalExpr_of_worldSub hsub hd) (evalArgs_of_worldSub hsub tl)

theorem evalFn_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F},
      EvalFn w1 nm args h r h' → EvalFn w2 nm args h r h'
  | _, _, _, _, _, .intro hp b =>
    .intro (hsub.prepare_sub _ _ _ hp) (evalExpr_of_worldSub hsub b)
  | _, _, _, _, _, .returned hp b =>
    .returned (hsub.prepare_sub _ _ _ hp) (evalExit_of_worldSub hsub b)

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
    .letBody (evalExpr_of_worldSub hsub v)
      (by rw [← hsub.aux.matchPattern_eq]; exact hm) (evalExit_of_worldSub hsub b)
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
    .matchBody (evalExpr_of_worldSub hsub v)
      (by rw [← hsub.aux.selectArm_eq]; exact hs) (evalExit_of_worldSub hsub b)

theorem evalArgsExit_of_worldSub {w1 w2 : World F} (hsub : WorldSub w1 w2) :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalArgsExit w1 types locals es h t r h' → EvalArgsExit w2 types locals es h t r h'
  | _, _, _, _, _, _, _, .head v => .head (evalExit_of_worldSub hsub v)
  | _, _, _, _, _, _, _, .tail hd tl =>
    .tail (evalExpr_of_worldSub hsub hd) (evalArgsExit_of_worldSub hsub tl)

end

/-- Overlay a list of `Prog` functions onto `base`, keeping `base`'s auxiliary tables and
all non-`Prog` library functions intact. -/
def overlayWorld (base : World F) (fns : List Fn) : World F where
  prepare nm args :=
    match fns.find? (fun f => qualified f.name == nm) with
    | some f =>
      if args.length == f.params.length then
        .ok ([], (f.params.map Prod.fst).zip args, qualifyExprF F f.body)
      else .error (.malformedValue (.tuple (args.map Value.type)))
    | none => base.prepare nm args
  typed := base.typed
  constant := base.constant
  constDepth := base.constDepth

omit [DecidableEq F] in
theorem sameAuxWorld_overlayWorld (base : World F) (fns : List Fn) :
    SameAuxWorld (overlayWorld base fns) base :=
  ⟨rfl, rfl, rfl⟩

omit [Field F] [DecidableEq F] in
theorem qualified_inj {a b : String} (h : qualified a = qualified b) : a = b := by
  unfold qualified moduleName at h
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  have h2 := List.append_cancel_left h1
  exact String.ext_iff.mpr h2

omit [Field F] [DecidableEq F] in
private theorem find?_eq_of_nodup {fns : List Fn} (hnd : (fns.map (·.name)).Nodup)
    {f : Fn} (hf : f ∈ fns) :
    fns.find? (fun g => qualified g.name == qualified f.name) = some f := by
  induction fns with
  | nil => cases hf
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | htl
    · simp
    · have hne : hd.name ≠ f.name := fun heq =>
        hnd.1 (heq ▸ List.mem_map.mpr ⟨f, htl, rfl⟩)
      have hqne : (qualified hd.name == qualified f.name) = false :=
        beq_false_of_ne fun heq => hne (qualified_inj heq)
      simp only [List.find?_cons, hqne]
      exact ih hnd.2 htl

omit [DecidableEq F] in
theorem overlayWorld_hasFns (base : World F) {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup) :
    WorldHasFns (overlayWorld base fns) fns := by
  intro f hf args types locals expr hprep
  simp only [overlayWorld, find?_eq_of_nodup hnd hf] at hprep
  split at hprep
  · next hlen =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at hprep
    obtain ⟨rfl, rfl, rfl⟩ := hprep
    simp only [beq_iff_eq] at hlen
    exact ⟨rfl, by simp [hlen], rfl, rfl⟩
  · cases hprep

omit [DecidableEq F] in
theorem overlayWorld_providesFns (base : World F) {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup) :
    WorldProvidesFns (overlayWorld base fns) fns := by
  intro f hf args hlen
  simp only [overlayWorld, find?_eq_of_nodup hnd hf]
  have hlen' : args.length = f.params.length := by simpa using hlen
  simp [hlen']

omit [DecidableEq F] in
theorem overlayWorld_prepare_other (base : World F) (fns : List Fn)
    {nm : String} (hnot : ∀ f ∈ fns, qualified f.name ≠ nm) (args : List (SourceValue F)) :
    (overlayWorld base fns).prepare nm args = base.prepare nm args := by
  have hnone : fns.find? (fun f => qualified f.name == nm) = none := by
    rw [List.find?_eq_none]
    intro f hf
    simp [beq_false_of_ne (hnot f hf)]
  simp [overlayWorld, hnone]

/-- Pure `List Char` check for `"Prog::"`-qualified names (reduces definitionally by `rfl`/`decide`). -/
def isProgQName (nm : String) : Bool :=
  nm.toList.take 6 == "Prog::".toList

omit [Field F] [DecidableEq F] in
theorem isProgQName_qualified (nm : String) : isProgQName (qualified nm) = true := by
  simp [isProgQName, qualified, moduleName, String.toList_append]

omit [DecidableEq F] in
theorem overlayWorld_prepare_nonProg (base : World F) (fns : List Fn)
    {nm : String} (hnot : isProgQName nm = false) (args : List (SourceValue F)) :
    (overlayWorld base fns).prepare nm args = base.prepare nm args := by
  apply overlayWorld_prepare_other
  intro f _ heq
  subst heq
  have h1 := isProgQName_qualified f.name
  rw [h1] at hnot
  cases hnot

omit [DecidableEq F] in
/-- **Stage 1 (`pruneUnreachable`) Soundness (World-Sub Embedding):**
Any `EvalFn` derivation in a world for `pruneUnreachable roots fns` lifts directly to
`EvalFn` in any world for `fns` (agreeing on auxiliary tables and external calls). -/
theorem pruneUnreachable_worldSub {wPruned wOrig : World F}
    {roots : List String} {fns : List Fn}
    (haux : SameAuxWorld wPruned wOrig)
    (hPrunedHas : WorldHasFns wPruned (pruneUnreachable roots fns))
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExt : ∀ nm args res,
      (∀ f ∈ pruneUnreachable roots fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wOrig.prepare nm args = .ok res) :
    WorldSub wPruned wOrig := by
  refine ⟨haux, fun nm args res hprep => ?_⟩
  by_cases hex : ∃ f ∈ pruneUnreachable roots fns, qualified f.name = nm
  · obtain ⟨f, hf, rfl⟩ := hex
    rcases res with ⟨types, locals, body⟩
    obtain ⟨rfl, hlen, rfl, rfl⟩ := hPrunedHas f hf args types locals body hprep
    have hfOrig : f ∈ fns := by
      unfold pruneUnreachable at hf
      exact (List.mem_filter.mp hf).1
    exact hOrigProv f hfOrig args hlen
  · exact hExt nm args res (fun f hf heq => hex ⟨f, hf, heq⟩) hprep

/-- **Stage 1 (`pruneUnreachable`) Backward Simulation:**
Any `EvalFn` derivation in the pruned world lifts verbatim to the unpruned world. -/
theorem pruneUnreachable_backward {wPruned wOrig : World F}
    {roots : List String} {fns : List Fn}
    (haux : SameAuxWorld wPruned wOrig)
    (hPrunedHas : WorldHasFns wPruned (pruneUnreachable roots fns))
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExt : ∀ nm args res,
      (∀ f ∈ pruneUnreachable roots fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  evalFn_of_worldSub (pruneUnreachable_worldSub haux hPrunedHas hOrigProv hExt) ev

/-- Concrete `overlayWorld` instantiation of `pruneUnreachable_backward`:
when `wPruned` only defines `Prog::` functions present in `pruneUnreachable roots fns`,
every `EvalFn` in `wPruned` lifts directly to `overlayWorld wPruned fns`. -/
theorem pruneUnreachable_overlay_backward {wPruned : World F}
    {roots : List String} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hPrunedHas : WorldHasFns wPruned (pruneUnreachable roots fns))
    (hOnlyPruned : ∀ f ∈ fns, f ∉ pruneUnreachable roots fns →
      ∀ args res, wPruned.prepare (qualified f.name) args ≠ .ok res)
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn (overlayWorld wPruned fns) nm args h r h' := by
  apply pruneUnreachable_backward (sameAuxWorld_overlayWorld wPruned fns).symm
    hPrunedHas (overlayWorld_providesFns wPruned hnd) _ ev
  intro nm' args' res hnot hprep
  have hnotFns : ∀ f ∈ fns, qualified f.name ≠ nm' := by
    intro f hf heq
    subst heq
    have hnotMem : f ∉ pruneUnreachable roots fns := fun hm => hnot f hm rfl
    exact hOnlyPruned f hf hnotMem args' res hprep
  rw [overlayWorld_prepare_other wPruned fns hnotFns]
  exact hprep

/-! ### Generic Depth-Indexed World Transfer (`evalExprN_transfer_world`) -/

mutual

/-- Transfer an `EvalExprN` derivation at depth `d` from `w1` to `w2` whenever `w1` and `w2`
have identical auxiliary tables and every call at depth `< d` transfers from `w1` to `w2`. -/
theorem evalExprN_transfer_world {w1 w2 : World F} {d : Nat}
    (haux : SameAuxWorld w1 w2)
    (hcall : ∀ d' < d, ∀ nm args h r h', EvalFnN w1 d' nm args h r h' → EvalFn w2 nm args h r h') :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {r : SourceValue F},
      EvalExprN w1 d types locals e h r h' → EvalExpr w2 types locals e h r h'
  | _, _, _, _, _, _, .literal => .literal
  | _, _, _, _, _, _, .var hl => .var hl
  | _, _, _, _, _, _, .global hl hi v =>
    .global (by rw [← haux.constant_eq]; exact hl) hi (evalExprN_transfer_world haux hcall v)
  | _, _, _, _, _, _, .tuple xs => .tuple (evalArgsN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, .array xs => .array (evalArgsN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, .repeat v => .repeat (evalExprN_transfer_world haux hcall v)
  | _, _, _, _, _, _, .index v hp => .index (evalExprN_transfer_world haux hcall v) hp
  | _, _, _, _, _, _, .slice v hs => .slice (evalExprN_transfer_world haux hcall v) hs
  | _, _, _, _, _, _, .builtin xs ha => .builtin (evalArgsN_transfer_world haux hcall xs) ha
  | _, _, _, _, _, _, .update xs ha => .update (evalArgsN_transfer_world haux hcall xs) ha
  | _, _, _, _, _, _, .record xs => .record (evalArgsN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, .member v hp => .member (evalExprN_transfer_world haux hcall v) hp
  | _, _, _, _, _, _, .construct xs => .construct (evalArgsN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, .constructAs xs => .constructAs (evalArgsN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, .project v hp => .project (evalExprN_transfer_world haux hcall v) hp
  | _, _, _, _, _, _, .letValue v hm b =>
    .letValue (evalExprN_transfer_world haux hcall v)
      (by rw [← haux.matchPattern_eq]; exact hm) (evalExprN_transfer_world haux hcall b)
  | _, _, _, _, _, _, .store v => .store (evalExprN_transfer_world haux hcall v)
  | _, _, _, _, _, _, .load v hl => .load (evalExprN_transfer_world haux hcall v) hl
  | _, _, _, _, _, _, .hint k ht =>
    .hint (evalExprN_transfer_world haux hcall k) (by rw [← haux.typed_eq]; exact ht)
  | _, _, _, _, _, _, .neg v hop => .neg (evalExprN_transfer_world haux hcall v) hop
  | _, _, _, _, _, _, .binary l r hop =>
    .binary (evalExprN_transfer_world haux hcall l) (evalExprN_transfer_world haux hcall r) hop
  | _, _, _, _, _, _, .call hlt xs cal =>
    .call (evalArgsN_transfer_world haux hcall xs) (hcall _ hlt _ _ _ _ _ cal)
  | _, _, _, _, _, _, .matchValue v hs b =>
    .matchValue (evalExprN_transfer_world haux hcall v)
      (by rw [← haux.selectArm_eq]; exact hs) (evalExprN_transfer_world haux hcall b)
  | _, _, _, _, _, _, .block b => .block (evalExprN_transfer_world haux hcall b)
  | _, _, _, _, _, _, .blockExit b => .blockExit (evalExitN_transfer_world haux hcall b)

theorem evalArgsN_transfer_world {w1 w2 : World F} {d : Nat}
    (haux : SameAuxWorld w1 w2)
    (hcall : ∀ d' < d, ∀ nm args h r h', EvalFnN w1 d' nm args h r h' → EvalFn w2 nm args h r h') :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgsN w1 d types locals es h vs h' → EvalArgs w2 types locals es h vs h'
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons hd tl =>
    .cons (evalExprN_transfer_world haux hcall hd) (evalArgsN_transfer_world haux hcall tl)

theorem evalExitN_transfer_world {w1 w2 : World F} {d : Nat}
    (haux : SameAuxWorld w1 w2)
    (hcall : ∀ d' < d, ∀ nm args h r h', EvalFnN w1 d' nm args h r h' → EvalFn w2 nm args h r h') :
    ∀ {types : Types} {locals : Environment F Nat} {e : Aiur.Generic.Expr F}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalExitN w1 d types locals e h t r h' → EvalExit w2 types locals e h t r h'
  | _, _, _, _, _, _, _, .exit v => .exit (evalExprN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .exitPayload v => .exitPayload (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromBlock hd b => .fromBlock hd (evalExitN_transfer_world haux hcall b)
  | _, _, _, _, _, _, _, .fromGlobal hl hi v =>
    .fromGlobal (by rw [← haux.constant_eq]; exact hl) hi (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromTuple xs => .fromTuple (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromArray xs => .fromArray (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromRepeat v => .fromRepeat (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromIndex v => .fromIndex (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromSlice v => .fromSlice (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromBuiltin xs => .fromBuiltin (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromUpdate xs => .fromUpdate (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromRecord xs => .fromRecord (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromMember v => .fromMember (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromConstruct xs => .fromConstruct (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromConstructAs xs => .fromConstructAs (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromProject v => .fromProject (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromLetValue v => .fromLetValue (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .letBody v hm b =>
    .letBody (evalExprN_transfer_world haux hcall v)
      (by rw [← haux.matchPattern_eq]; exact hm) (evalExitN_transfer_world haux hcall b)
  | _, _, _, _, _, _, _, .fromStore v => .fromStore (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromLoad v => .fromLoad (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromHint v => .fromHint (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .fromNeg v => .fromNeg (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .binaryLeft v => .binaryLeft (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .binaryRight l r =>
    .binaryRight (evalExprN_transfer_world haux hcall l) (evalExitN_transfer_world haux hcall r)
  | _, _, _, _, _, _, _, .fromCall xs => .fromCall (evalArgsExitN_transfer_world haux hcall xs)
  | _, _, _, _, _, _, _, .fromMatchValue v => .fromMatchValue (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .matchBody v hs b =>
    .matchBody (evalExprN_transfer_world haux hcall v)
      (by rw [← haux.selectArm_eq]; exact hs) (evalExitN_transfer_world haux hcall b)

theorem evalArgsExitN_transfer_world {w1 w2 : World F} {d : Nat}
    (haux : SameAuxWorld w1 w2)
    (hcall : ∀ d' < d, ∀ nm args h r h', EvalFnN w1 d' nm args h r h' → EvalFn w2 nm args h r h') :
    ∀ {types : Types} {locals : Environment F Nat} {es : List (Aiur.Generic.Expr F)}
      {h h' : Heap F} {t : ExitTarget} {r : SourceValue F},
      EvalArgsExitN w1 d types locals es h t r h' → EvalArgsExit w2 types locals es h t r h'
  | _, _, _, _, _, _, _, .head v => .head (evalExitN_transfer_world haux hcall v)
  | _, _, _, _, _, _, _, .tail hd tl =>
    .tail (evalExprN_transfer_world haux hcall hd) (evalArgsExitN_transfer_world haux hcall tl)

end

/-- **Generic Program-Body Transformation Lifting Lemma (Untyped):**
Lifts any per-function same-world body backward simulation `f'.body → f.body`
to a full world-level `EvalFn wOpt → EvalFn wOrig` backward simulation. -/
theorem world_transformBodies_backward {wOpt wOrig : World F}
    {fns fns' : List Fn}
    (haux : SameAuxWorld wOpt wOrig)
    (hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params) fns fns')
    (hOptHas : WorldHasFns wOpt fns')
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExt : ∀ nm args res,
      (∀ f' ∈ fns', qualified f'.name ≠ nm) →
      wOpt.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hPlain : ∀ f' ∈ fns', isPlainExpr f'.body = true)
    (hBodySim : ∀ f f', f ∈ fns → f' ∈ fns' → f'.name = f.name → f'.params = f.params →
      ∀ args h r h', args.length = f.params.length →
        EvalExpr wOrig [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f'.body) h r h' →
        EvalExpr wOrig [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f.body) h r h')
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wOpt nm args h r h') :
    EvalFn wOrig nm args h r h' := by
  have hPair : ∀ f' ∈ fns', ∃ f ∈ fns, f'.name = f.name ∧ f'.params = f.params := by
    clear hOptHas hOrigProv hExt hPlain hBodySim ev
    induction hrel with
    | nil => intro _ h; cases h
    | cons h1 _ ih =>
      intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | htl
      · exact ⟨_, List.mem_cons_self, h1.1, h1.2⟩
      · obtain ⟨f, hf, hn, hp⟩ := ih f' htl
        exact ⟨f, List.mem_cons_of_mem _ hf, hn, hp⟩
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  revert nm args h h' r ev evN
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro nm args h h' r _ evN
    have hcall : ∀ d' < d, ∀ nm' args' h1 r1 h2,
        EvalFnN wOpt d' nm' args' h1 r1 h2 → EvalFn wOrig nm' args' h1 r1 h2 :=
      fun d' hlt nm' args' h1 r1 h2 e => ih d' hlt e.toEvalFn e
    by_cases hex : ∃ f' ∈ fns', qualified f'.name = nm
    · obtain ⟨f', hf', rfl⟩ := hex
      obtain ⟨f, hf, hnm, hpar⟩ := hPair f' hf'
      cases evN with
      | intro prep body =>
        obtain ⟨rfl, hlen, rfl, rfl⟩ := hOptHas f' hf' args _ _ _ prep
        have bodyOrig := evalExprN_transfer_world haux hcall body
        have hlen' : args.length = f.params.length := by
          rw [← hpar]; simpa using hlen
        have bodyOrig' : EvalExpr wOrig [] ((f.params.map Prod.fst).zip args)
            (qualifyExprF F f'.body) h r h' := by
          rw [← hpar]; exact bodyOrig
        have bodySim := hBodySim f f' hf hf' hnm hpar args h r h' hlen' bodyOrig'
        have prepOrig : wOrig.prepare (qualified f'.name) args =
            .ok ([], (f.params.map Prod.fst).zip args, qualifyExprF F f.body) := by
          rw [hnm]
          exact hOrigProv f hf args (by simpa using hlen')
        exact .intro prepOrig bodySim
      | returned prep body =>
        obtain ⟨rfl, _, rfl, rfl⟩ := hOptHas f' hf' args _ _ _ prep
        exact False.elim (no_evalExit_of_plain
          (by rw [isPlainExpr_qualifyExprF]; exact hPlain f' hf') body.toEvalExit)
    · have hnot : ∀ f' ∈ fns', qualified f'.name ≠ nm := fun f' hf' heq => hex ⟨f', hf', heq⟩
      cases evN with
      | intro prep body =>
        exact .intro (hExt nm args _ hnot prep) (evalExprN_transfer_world haux hcall body)
      | returned prep body =>
        exact .returned (hExt nm args _ hnot prep) (evalExitN_transfer_world haux hcall body)

end WorldInfra

/-! ## Section 2: Clean Expressions, Pattern Bindings & `EvalExpr` Local-Env Congruence -/

section CleanAndLocals

mutual

/-- Simple patterns emitted by `TypedLower` (no `.global`, `.orElse`, `.load`, `.repeat`,
`.record`, or `.constructAs`). -/
def isSimplePat : Pat → Bool
  | .literal _ | .wildcard | .bind _ => true
  | .tuple ps | .array ps | .construct _ _ ps => isSimplePatList ps
  | _ => false

def isSimplePatList : List Pat → Bool
  | [] => true
  | p :: ps => isSimplePat p && isSimplePatList ps

end

mutual

/-- Plain expressions (`isPlainExpr`) whose `letValue` and `matchValue` patterns are all
`isSimplePat`. -/
def isCleanExpr : Expr → Bool
  | .control .. | .global .. => false
  | .literal _ | .var _ => true
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => isCleanList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => isCleanExpr x
  | .binary _ l r => isCleanExpr l && isCleanExpr r
  | .letValue p v b => isSimplePat p && isCleanExpr v && isCleanExpr b
  | .matchValue s arms => isCleanExpr s && isCleanArms arms

def isCleanList : List Expr → Bool
  | [] => true
  | x :: xs => isCleanExpr x && isCleanList xs

def isCleanArms : List (Pat × Expr) → Bool
  | [] => true
  | (p, b) :: rest => isSimplePat p && isCleanExpr b && isCleanArms rest

end

theorem isSimplePatList_iff {ps : List Pat} :
    isSimplePatList ps = true ↔ ∀ p ∈ ps, isSimplePat p = true := by
  induction ps with
  | nil => simp [isSimplePatList]
  | cons p tl ih =>
    simp only [isSimplePatList, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

theorem isCleanList_iff {xs : List Expr} :
    isCleanList xs = true ↔ ∀ x ∈ xs, isCleanExpr x = true := by
  induction xs with
  | nil => simp [isCleanList]
  | cons x tl ih =>
    simp only [isCleanList, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

theorem isCleanArms_iff {arms : List (Pat × Expr)} :
    isCleanArms arms = true ↔ ∀ a ∈ arms, isSimplePat a.1 = true ∧ isCleanExpr a.2 = true := by
  induction arms with
  | nil => simp [isCleanArms]
  | cons a tl ih =>
    rcases a with ⟨p, b⟩
    simp only [isCleanArms, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

mutual

theorem isPlainExpr_of_isCleanExpr : ∀ {e : Expr}, isCleanExpr e = true → isPlainExpr e = true
  | .control .., h | .global .., h => by simp [isCleanExpr] at h
  | .literal _, _ | .var _, _ => rfl
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h | .call _ _ xs, h =>
    isPlainList_of_isCleanList h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    isPlainExpr_of_isCleanExpr (e := x) h
  | .binary _ l r, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [isPlainExpr, isPlainExpr_of_isCleanExpr h.1, isPlainExpr_of_isCleanExpr h.2]
  | .letValue _ v b, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [isPlainExpr, isPlainExpr_of_isCleanExpr h.1.2, isPlainExpr_of_isCleanExpr h.2]
  | .matchValue s arms, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [isPlainExpr, isPlainExpr_of_isCleanExpr h.1, isPlainArms_of_isCleanArms h.2]

theorem isPlainList_of_isCleanList : ∀ {xs : List Expr}, isCleanList xs = true → isPlainList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanList, Bool.and_eq_true] at h
    simp [isPlainList, isPlainExpr_of_isCleanExpr h.1, isPlainList_of_isCleanList h.2]

theorem isPlainArms_of_isCleanArms :
    ∀ {arms : List (Pat × Expr)}, isCleanArms arms = true → isPlainArms arms = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [isCleanArms, Bool.and_eq_true] at h
    simp [isPlainArms, isPlainExpr_of_isCleanExpr h.1.2, isPlainArms_of_isCleanArms h.2]

end

mutual

/-- On simple patterns, `InlineFuse.patBoundVars` and `Peephole.patBoundNames` coincide. -/
theorem patBoundVars_eq_patBoundNames :
    ∀ {p : Pat}, isSimplePat p = true → patBoundVars p = Peephole.patBoundNames p
  | .literal _, _ | .wildcard, _ | .bind _, _ => rfl
  | .tuple ps, h | .array ps, h | .construct _ _ ps, h =>
    patListBoundVars_eq_patBoundNamesList h
  | .global .., h | .load _, h | .orElse .., h | .repeat .., h
  | .record .., h | .constructAs .., h => by simp [isSimplePat] at h

theorem patListBoundVars_eq_patBoundNamesList :
    ∀ {ps : List Pat}, isSimplePatList ps = true → patListBoundVars ps = Peephole.patBoundNamesList ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [isSimplePatList, Bool.and_eq_true] at h
    simp [patListBoundVars, Peephole.patBoundNamesList,
      patBoundVars_eq_patBoundNames h.1, patListBoundVars_eq_patBoundNamesList h.2]

end

mutual

/-- On clean expressions, `InlineFuse.hasFreeVar` and `Peephole.occursFree` coincide. -/
theorem hasFreeVar_eq_occursFree (v : String) :
    ∀ {e : Expr}, isCleanExpr e = true → hasFreeVar v e = Peephole.occursFree v e
  | .control .., h | .global .., h => by simp [isCleanExpr] at h
  | .literal _, _ | .var _, _ => rfl
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h | .call _ _ xs, h =>
    hasFreeVarList_eq_occursFreeList v h
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h =>
    hasFreeVar_eq_occursFree v (e := x) h
  | .binary _ l r, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [hasFreeVar, Peephole.occursFree,
      hasFreeVar_eq_occursFree v h.1, hasFreeVar_eq_occursFree v h.2]
  | .letValue p x b, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [hasFreeVar, Peephole.occursFree, patBoundVars_eq_patBoundNames h.1.1,
      hasFreeVar_eq_occursFree v h.1.2, hasFreeVar_eq_occursFree v h.2]
  | .matchValue s arms, h => by
    simp only [isCleanExpr, Bool.and_eq_true] at h
    simp [hasFreeVar, Peephole.occursFree,
      hasFreeVar_eq_occursFree v h.1, hasFreeVarArms_eq_occursFreeArms v h.2]

theorem hasFreeVarList_eq_occursFreeList (v : String) :
    ∀ {xs : List Expr}, isCleanList xs = true → hasFreeVarList v xs = Peephole.occursFreeList v xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [isCleanList, Bool.and_eq_true] at h
    simp [hasFreeVarList, Peephole.occursFreeList,
      hasFreeVar_eq_occursFree v h.1, hasFreeVarList_eq_occursFreeList v h.2]

theorem hasFreeVarArms_eq_occursFreeArms (v : String) :
    ∀ {arms : List (Pat × Expr)}, isCleanArms arms = true →
      hasFreeVarArms v arms = Peephole.occursFreeArms v arms
  | [], _ => rfl
  | (p, b) :: rest, h => by
    simp only [isCleanArms, Bool.and_eq_true] at h
    simp [hasFreeVarArms, Peephole.occursFreeArms, patBoundVars_eq_patBoundNames h.1.1,
      hasFreeVar_eq_occursFree v h.1.2, hasFreeVarArms_eq_occursFreeArms v h.2]

end

section PatternAndLocals

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
theorem matchListWith_map {α β : Type}
    (f : β → SourceValue F → Except EvalError (Option (Environment F Nat))) (g : α → β) :
    ∀ (l : List α) (vs : List (SourceValue F)),
      matchListWith f (l.map g) vs = matchListWith (fun a v => f (g a) v) l vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: tl, v :: vt => by
    simp only [List.map_cons, matchListWith, bind, Except.bind]
    cases f (g a) v with
    | error _ => rfl
    | ok o => cases o <;> simp [matchListWith_map]

omit [Field F] [DecidableEq F] in
theorem matchListWith_attach {α : Type}
    (f : α → SourceValue F → Except EvalError (Option (Environment F Nat))) :
    ∀ (l : List α) (vs : List (SourceValue F)),
      matchListWith (fun p val => f p.val val) l.attach vs = matchListWith f l vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: tl, v :: vt => by
    simp only [List.attach_cons, matchListWith, bind, Except.bind]
    cases f a v with
    | error _ => rfl
    | ok o =>
      cases o with
      | none => rfl
      | some _ =>
        rw [matchListWith_map, matchListWith_attach f tl vt]

omit [DecidableEq F] in
theorem map_qualifyExprF (xs : List Expr) :
    List.map (Aiur.Generic.Expr.map (Nat.cast : Nat → F)) (List.map qualifyExpr xs) =
      xs.map (qualifyExprF F) := by
  simp [qualifyExprF, List.map_map, Function.comp_def]

omit [DecidableEq F] in
theorem map_qualifyArmsF (arms : List (Pat × Expr)) :
    List.map (fun arm => (Aiur.Generic.Pattern.map (Nat.cast : Nat → F) arm.1,
        Aiur.Generic.Expr.map (Nat.cast : Nat → F) arm.2))
      (List.map (fun arm => (qualifyPat arm.1, qualifyExpr arm.2)) arms) =
    arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2) := by
  simp [qualifyPatF, qualifyExprF, List.map_map, Function.comp_def]

omit [Field F] [DecidableEq F] in
theorem find?_append_agree {bs loc1 loc2 : Environment F Nat} {x : String}
    (h : x ∉ bs.map Prod.fst → loc1.find? (·.1 == x) = loc2.find? (·.1 == x)) :
    (bs ++ loc1).find? (·.1 == x) = (bs ++ loc2).find? (·.1 == x) := by
  rw [List.find?_append, List.find?_append]
  cases hf : bs.find? (·.1 == x) with
  | some _ => rfl
  | none =>
    simp only [Option.none_or]
    apply h
    intro hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
    have hnone := List.find?_eq_none.mp hf p hp
    simp at hnone

mutual

/-- Every simple pattern binds the exact list of variable names in `patBoundVars`. -/
theorem matchPattern_names_of_simple {world : World F} {h : Heap F} :
    ∀ {p : Pat} {v : SourceValue F} {bs : Environment F Nat},
      isSimplePat p = true →
      world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) →
      bs.map Prod.fst = patBoundVars p
  | .literal c, v, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
    cases v with
    | field x =>
      by_cases hx : (c : F) = x
      · subst hx; simp [Aiur.Pattern.bindings] at hm; subst hm; rfl
      · simp [Aiur.Pattern.bindings, hx] at hm
    | tuple _ | ptr _ _ | construct _ _ _ => simp [Aiur.Pattern.bindings] at hm
  | .wildcard, _, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; rfl
  | .bind x, _, bs, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; rfl
  | .tuple ps, v, bs, hs, hm => by
    cases v with
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
    | tuple vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases hlen : (ps.length != vals.length) = true
      · simp [hlen, pure, Except.pure] at hm
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        exact matchPatternList_names_of_simple hs hm
  | .array ps, v, bs, hs, hm => by
    cases v with
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
    | tuple vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases hlen : (ps.length != vals.length) = true
      · simp [hlen, pure, Except.pure] at hm
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        exact matchPatternList_names_of_simple hs hm
  | .construct ty ctor ps, v, bs, hs, hm => by
    cases v with
    | field _ | ptr _ _ | tuple _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
    | construct nm c vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases htest : (nm != constructorName [] (qualifyTy ty) || c != ctor || (ps.length != vals.length)) = true
      · simp [htest, pure, Except.pure] at hm
      · simp only [htest, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        exact matchPatternList_names_of_simple hs hm
  | .global .., _, _, hs, _ | .load _, _, _, hs, _ | .orElse .., _, _, hs, _
  | .repeat .., _, _, hs, _ | .record .., _, _, hs, _ | .constructAs .., _, _, hs, _ => by
    simp [isSimplePat] at hs

theorem matchPatternList_names_of_simple {world : World F} {h : Heap F} :
    ∀ {qs : List Pat} {vs : List (SourceValue F)} {bs : Environment F Nat},
      isSimplePatList qs = true →
      matchListWith (fun q val => world.matchPattern [] h (qualifyPatF F q) val) qs vs = .ok (some bs) →
      bs.map Prod.fst = patListBoundVars qs
  | [], [], bs, _, hml => by
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hml
    subst hml; rfl
  | [], _ :: _, _, _, hml | _ :: _, [], _, _, hml => by
    simp [matchListWith, pure, Except.pure] at hml
  | q :: qt, v :: vt, bs, hsp, hml => by
    simp only [isSimplePatList, Bool.and_eq_true] at hsp
    simp only [matchListWith, bind, Except.bind] at hml
    cases h1 : world.matchPattern [] h (qualifyPatF F q) v with
    | error _ => simp [h1] at hml
    | ok o1 =>
      cases o1 with
      | none => simp [h1, pure, Except.pure] at hml
      | some b1 =>
        simp only [h1] at hml
        cases h2 : matchListWith (fun q val => world.matchPattern [] h (qualifyPatF F q) val) qt vt with
        | error _ => simp [h2] at hml
        | ok o2 =>
          cases o2 with
          | none => simp [h2, pure, Except.pure] at hml
          | some b2 =>
            simp only [h2, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hml
            subst hml
            simp [patListBoundVars,
              matchPattern_names_of_simple hsp.1 h1,
              matchPatternList_names_of_simple hsp.2 h2]

end

theorem selectArm_map_inv {world : World F} {h : Heap F} {v : SourceValue F} :
    ∀ {arms : List (Pat × Expr)} {bs : Environment F Nat} {bodyF : Aiur.Generic.Expr F},
      SourceSemantics.selectArm world [] h v
        (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) = .ok (some (bs, bodyF)) →
      ∃ p b, (p, b) ∈ arms ∧ bodyF = qualifyExprF F b ∧
        world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs)
  | [], _, _, hsel => by simp [SourceSemantics.selectArm, pure, Except.pure] at hsel
  | (p, b) :: rest, bs, bodyF, hsel => by
    simp only [List.map_cons, SourceSemantics.selectArm, bind, Except.bind] at hsel
    cases hm : world.matchPattern [] h (qualifyPatF F p) v with
    | error _ => simp [hm] at hsel
    | ok o =>
      cases o with
      | some bs' =>
        simp only [hm, pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨p, b, List.mem_cons_self, rfl, hm⟩
      | none =>
        simp only [hm] at hsel
        obtain ⟨p', b', hmem, heq, hm'⟩ := selectArm_map_inv hsel
        exact ⟨p', b', List.mem_cons_of_mem _ hmem, heq, hm'⟩

mutual

/-- Local-environment congruence for `EvalExpr`: if `loc1` and `loc2` agree on all
free variables of a clean expression `e`, any `EvalExpr` derivation in `loc1` transfers to `loc2`. -/
theorem evalExpr_localsAgree {world : World F} :
    ∀ {e : Expr} {loc1 loc2 : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      isCleanExpr e = true →
      (∀ x, hasFreeVar x e = true → loc1.find? (·.1 == x) = loc2.find? (·.1 == x)) →
      EvalExpr world [] loc1 (qualifyExprF F e) h r h' →
      EvalExpr world [] loc2 (qualifyExprF F e) h r h'
  | .control .., _, _, _, _, _, hc, _, _ | .global .., _, _, _, _, _, hc, _, _ => by
    simp [isCleanExpr] at hc
  | .literal _, _, _, _, _, _, _, _, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
    exact .literal
  | .var nm, _, _, _, _, _, _, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    obtain ⟨hl, rfl⟩ := evalExpr_var_inv ev
    exact .var (by rw [← hag nm (by simp [hasFreeVar])]; exact hl)
  | .tuple xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple items => exact .tuple (evalArgs_localsAgree hc (fun x hx => hag x hx) items)
  | .array xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array items => exact .array (evalArgs_localsAgree hc (fun x hx => hag x hx) items)
  | .repeat x n, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item => exact .repeat (evalExpr_localsAgree hc hag item)
  | .index x i, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp => exact .index (evalExpr_localsAgree hc hag item) hp
  | .slice x s t, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs => exact .slice (evalExpr_localsAgree hc hag item) hs
  | .builtin op xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin items ha => exact .builtin (evalArgs_localsAgree hc (fun x hx => hag x hx) items) ha
  | .update ps xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | update items ha => exact .update (evalArgs_localsAgree hc (fun x hx => hag x hx) items) ha
  | .record hd xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | record items => exact .record (evalArgs_localsAgree hc (fun x hx => hag x hx) items)
  | .member x f, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | member item hp => exact .member (evalExpr_localsAgree hc hag item) hp
  | .construct n ts c xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct items => exact .construct (evalArgs_localsAgree hc (fun x hx => hag x hx) items)
  | .constructAs ps t c xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | constructAs items => exact .constructAs (evalArgs_localsAgree hc (fun x hx => hag x hx) items)
  | .project x i, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp => exact .project (evalExpr_localsAgree hc hag item) hp
  | .store x, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item => exact .store (evalExpr_localsAgree hc hag item)
  | .load x, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl => exact .load (evalExpr_localsAgree hc hag item) hl
  | .hint t x ch, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht => exact .hint (evalExpr_localsAgree (e := x) hc hag item) ht
  | .neg x, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop => exact .neg (evalExpr_localsAgree hc hag item) hop
  | .binary op l r, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary el er hop =>
      exact .binary
        (evalExpr_localsAgree hc.1 (fun x hx => hag x (by simp [hasFreeVar, hx])) el)
        (evalExpr_localsAgree hc.2 (fun x hx => hag x (by simp [hasFreeVar, hx])) er) hop
  | .call nm ts xs, _, _, _, _, _, hc, hag, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | call items hcal => exact .call (evalArgs_localsAgree hc (fun x hx => hag x hx) items) hcal
  | .letValue p v b, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    obtain ⟨⟨hp, hv⟩, hb⟩ := hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | letValue evV hm evB =>
      have hnames := matchPattern_names_of_simple hp hm
      refine .letValue
        (evalExpr_localsAgree hv (fun x hx => hag x (by simp [hasFreeVar, hx])) evV) hm ?_
      apply evalExpr_localsAgree hb _ evB
      intro x hx
      apply find?_append_agree
      intro hnotmem
      rw [hnames] at hnotmem
      exact hag x (by simp [hasFreeVar, hnotmem, hx])
  | .matchValue s arms, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | matchValue evS hsel evB =>
      have hsel' := hsel
      rw [map_qualifyArmsF] at hsel'
      obtain ⟨p, b, hmem, rfl, hm⟩ := selectArm_map_inv hsel'
      have hpa := (isCleanArms_iff.mp hc.2) (p, b) hmem
      have hnames := matchPattern_names_of_simple hpa.1 hm
      refine .matchValue
        (evalExpr_localsAgree hc.1 (fun x hx => hag x (by simp [hasFreeVar, hx])) evS) hsel ?_
      apply evalExpr_localsAgree hpa.2 _ evB
      intro x hx
      apply find?_append_agree
      intro hnotmem
      rw [hnames] at hnotmem
      have hmemArm : hasFreeVarArms x arms = true := by
        clear evS hsel hsel' evB hm hnames hc hag
        induction arms with
        | nil => cases hmem
        | cons hd tl ih =>
          rcases List.mem_cons.mp hmem with rfl | htl
          · simp [hasFreeVarArms, hnotmem, hx]
          · simp [hasFreeVarArms, ih htl]
      exact hag x (by simp [hasFreeVar, hmemArm])
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem hmem; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_localsAgree {world : World F} :
    ∀ {xs : List Expr} {loc1 loc2 : Environment F Nat} {h h' : Heap F} {ws : List (SourceValue F)},
      isCleanList xs = true →
      (∀ x, hasFreeVarList x xs = true → loc1.find? (·.1 == x) = loc2.find? (·.1 == x)) →
      EvalArgs world [] loc1 (xs.map (qualifyExprF F)) h ws h' →
      EvalArgs world [] loc2 (xs.map (qualifyExprF F)) h ws h'
  | [], _, _, _, _, _, _, _, ev => by cases ev; exact .nil
  | a :: tl, _, _, _, _, _, hc, hag, ev => by
    simp only [isCleanList, Bool.and_eq_true] at hc
    cases ev with
    | cons hd rest =>
      exact .cons
        (evalExpr_localsAgree hc.1 (fun x hx => hag x (by simp [hasFreeVarList, hx])) hd)
        (evalArgs_localsAgree hc.2 (fun x hx => hag x (by simp [hasFreeVarList, hx])) rest)
termination_by xs => sizeOf xs

end

end PatternAndLocals

end CleanAndLocals

/-! ## Section 3: Sound `UInt32` Value Typing (`ValOk`, `HasTy`, `U32WorldSpec`) -/

section TypingAndU32Spec

/-- `UInt32::Compact` opaque type name. -/
def compactTy : Lower.Ty := .named "UInt32::Compact" []

/-- Function signature table mapping qualified function names to `(paramTys, retTy)`. -/
abbrev FnSigs := String → Option (List Lower.Ty × Lower.Ty)

/-- Local typing environment mapping variable names to `Lower.Ty`. -/
abbrev TyEnv := List (String × Lower.Ty)

/-- Look up constructor field types in `enums`. -/
def findCtorFields (enums : List Aiur.Generic.EnumDecl) (en ctor : String) : Option (List Lower.Ty) :=
  match enums.find? (·.name == en) with
  | some ed => (ed.constructors.find? (·.name == ctor)).map (·.fields)
  | none => none

/-- Types built solely from raw `Field`s (safe as `.hint` target types: `ValOk` is trivially `True`). -/
def isFieldOnlyTy : Lower.Ty → Bool
  | .field => true
  | .array t _ => isFieldOnlyTy t
  | .tuple ts => isFieldOnlyTyList ts
  | _ => false
where
  isFieldOnlyTyList : List Lower.Ty → Bool
    | [] => true
    | t :: ts => isFieldOnlyTy t && isFieldOnlyTyList ts

/-- Fixed signatures of `UInt8` / `UInt32` / `UInt64` / `U8Byte` library functions. -/
def libFnSig : FnSigs
  | "UInt32::add" | "UInt32::sub" | "UInt32::xor" | "UInt32::and" | "UInt32::or"
  | "UInt32::xor_rotr7" | "UInt32::xor_rotr12" => some ([u32Ty, u32Ty], u32Ty)
  | "UInt32::add3" => some ([u32Ty, u32Ty, u32Ty], u32Ty)
  | "UInt32::rotr8" | "UInt32::rotr16" => some ([u32Ty], u32Ty)
  | "UInt32::to_bytes" => some ([u32Ty], .array u8Ty 4)
  | "UInt32::from_bytes" => some ([.array u8Ty 4], u32Ty)
  | "UInt32::compact" => some ([u32Ty], compactTy)
  | "UInt32::compact_field" => some ([compactTy], .field)
  | "UInt32::from_fields" => some ([.array .field 4], u32Ty)
  | "UInt32::from_field" => some ([.field], u32Ty)
  | "UInt32::less_than" => some ([u32Ty, u32Ty], .field)
  | "UInt32::sub_borrow" => some ([compactTy, compactTy], .tuple [u32Ty, .field])
  | "UInt32::compact_less_than" => some ([compactTy, compactTy], .field)
  | "UInt32::less_than_fields" => some ([.field, .field], .field)
  | "UInt32::compact_from_field" => some ([.field], compactTy)
  | "UInt32::expand" => some ([compactTy], u32Ty)
  | "UInt8::from_fields" => some ([.field, .field], .tuple [u8Ty, u8Ty])
  | "UInt8::to_field" => some ([u8Ty], .field)
  | "UInt8::xor" | "UInt8::and" | "UInt8::or" => some ([u8Ty, u8Ty], u8Ty)
  | "U8Byte::check" => some ([.field], .tuple [])
  | "UInt64::from_field" => some ([.field], u64Ty)
  | "UInt64::to_field" | "UInt64::is_zero" => some ([u64Ty], .field)
  | "UInt64::sub_with_borrow" => some ([u64Ty, u64Ty], .tuple [u64Ty, .field])
  | "UInt64::mul" => some ([u64Ty, u64Ty], .tuple [u64Ty, u64Ty])
  | "UInt64::and" | "UInt64::or" | "UInt64::xor" => some ([u64Ty, u64Ty], u64Ty)
  | _ => none

theorem libFnSig_nonProg {qnm : String} {sig : List Lower.Ty × Lower.Ty}
    (h : libFnSig qnm = some sig) : isProgQName qnm = false := by
  unfold libFnSig at h
  split at h <;> try cases h
  all_goals rfl

/-- Combined signature lookup for `Prog` functions `fns` plus standard library functions. -/
def fnSigsOf (fns : List Fn) : FnSigs := fun qnm =>
  match fns.find? (fun f => qualified f.name == qnm) with
  | some f => some (f.params.map Prod.snd, f.result)
  | none => libFnSig qnm

theorem fnSigsOf_eq_of_sameSigs {fns1 fns2 : List Fn}
    (h : List.Forall₂ (fun f1 f2 => f2.name = f1.name ∧ f2.params = f1.params ∧ f2.result = f1.result)
      fns1 fns2) :
    fnSigsOf fns2 = fnSigsOf fns1 := by
  funext qnm
  unfold fnSigsOf
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    simp only [List.find?_cons, h1.1]
    cases (qualified _ == qnm)
    · exact ih
    · simp [h1.2.1, h1.2.2]

private theorem mem_zip_of_getElem? {α β : Type} {xs : List α} {ys : List β} {i : Nat}
    {a : α} {b : β} (hx : xs[i]? = some a) (hy : ys[i]? = some b) :
    (a, b) ∈ xs.zip ys := by
  obtain ⟨hi1, rfl⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hi2, rfl⟩ := List.getElem?_eq_some_iff.mp hy
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp [hi1, hi2], by simp⟩

section ValOkDef

variable {F : Type} [Field F]

/-- Sound `UInt32` value validity invariant indexed by `(bound, sizeOf v)` so recursive
enum pointers (`&Obj`, `&D<d>`) terminate cleanly without coinduction or separate heap invariants:
- `UInt32::U32` and `[UInt8::U8; 4]`: exact `∃ n, isU32Val n v` (4 bytes `< 256`);
- `UInt32::Compact`: `∃ n < 2^32, v = .field n`;
- `UInt8::U8`: `∃ b < 256, v = .field b`;
- `.field`, `UInt64::U64`, `.array .field n`, `.tuple [.field, ...]`: trivially `True`! -/
def ValOk (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (bound : Nat) :
    Lower.Ty → SourceValue F → Prop
  | .named en [], v =>
    if en == "UInt32::U32" then ∃ n, isU32Val n v
    else if en == "UInt32::Compact" then ∃ n : Nat, n < U32.base ∧ v = .field (n : F)
    else if en == "UInt8::U8" then ∃ b : Nat, b < 256 ∧ v = .field (b : F)
    else if en == "UInt64::U64" then True
    else match v with
      | .construct qen ctor vs =>
        qen = qualifyName en →
        match findCtorFields enums en ctor with
        | some fts => ∀ p ∈ fts.zip vs, ValOk enums h bound p.1 p.2
        | none => True
      | _ => True
  | .array t n, v =>
    if t == u8Ty && n == 4 then ∃ k, isU32Val k v
    else match v with
      | .tuple vs => ∀ x ∈ vs, ValOk enums h bound t x
      | _ => True
  | .tuple ts, v =>
    match v with
    | .tuple vs => ∀ p ∈ ts.zip vs, ValOk enums h bound p.1 p.2
    | _ => True
  | .ptr t, v =>
    match v with
    | .ptr _ addr => ∃ (_ : addr < bound) (w : SourceValue F), h[addr]? = some w ∧ ValOk enums h addr t w
    | _ => True
  | _, _ => True
termination_by _ v => (bound, sizeOf v)
decreasing_by
  all_goals simp_wf
  · right
    have hmem : p.2 ∈ vs := (List.of_mem_zip ‹_›).2
    have h1 := List.sizeOf_lt_of_mem hmem
    have _ : sizeOf vs < sizeOf (Value.construct qen ctor vs) := by
      simp [Value.construct.sizeOf_spec]
    omega
  · right
    have h1 := List.sizeOf_lt_of_mem ‹_ ∈ _›
    have _ : sizeOf vs < sizeOf (Value.tuple vs) := by
      simp [Value.tuple.sizeOf_spec]
    omega
  · right
    have hmem : p.2 ∈ vs := (List.of_mem_zip ‹_›).2
    have h1 := List.sizeOf_lt_of_mem hmem
    have _ : sizeOf vs < sizeOf (Value.tuple vs) := by
      simp [Value.tuple.sizeOf_spec]
    omega
  · left; assumption

@[simp] theorem ValOk_field (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (v : SourceValue F) : ValOk enums h b .field v ↔ True := by
  unfold ValOk; simp

@[simp] theorem ValOk_u32 (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (v : SourceValue F) : ValOk enums h b u32Ty v ↔ ∃ n, isU32Val n v := by
  unfold ValOk; simp [u32Ty]

@[simp] theorem ValOk_compact (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (v : SourceValue F) : ValOk enums h b compactTy v ↔ ∃ n : Nat, n < U32.base ∧ v = .field (n : F) := by
  unfold ValOk; simp [compactTy]

@[simp] theorem ValOk_u8 (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (v : SourceValue F) : ValOk enums h b u8Ty v ↔ ∃ k : Nat, k < 256 ∧ v = .field (k : F) := by
  unfold ValOk; simp [u8Ty]

@[simp] theorem ValOk_u8Array4 (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (v : SourceValue F) : ValOk enums h b (.array u8Ty 4) v ↔ ∃ n, isU32Val n v := by
  unfold ValOk; simp [u8Ty]

@[simp] theorem ValOk_u64 (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (v : SourceValue F) : ValOk enums h b u64Ty v ↔ True := by
  unfold ValOk; simp [u64Ty]

theorem ValOk.mono {enums : List Aiur.Generic.EnumDecl} {h1 h2 : Heap F}
    (hext : Heap.Extends h1 h2) :
    ∀ {b1 b2 : Nat} {t : Lower.Ty} {v : SourceValue F},
      b1 ≤ b2 → ValOk enums h1 b1 t v → ValOk enums h2 b2 t v
  | b1, b2, .named en [], v, hle, hv => by
    unfold ValOk at hv ⊢
    by_cases h1 : en = "UInt32::U32"
    · subst h1; simpa using hv
    · by_cases h2 : en = "UInt32::Compact"
      · subst h2; simpa using hv
      · by_cases h3 : en = "UInt8::U8"
        · subst h3; simpa using hv
        · by_cases h4 : en = "UInt64::U64"
          · subst h4; simp
          · simp only [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3,
              beq_false_of_ne h4, Bool.false_eq_true, ↓reduceIte] at hv ⊢
            cases v with
            | construct qen ctor vs =>
              intro hq
              have hv' := hv hq
              cases hf : findCtorFields enums en ctor with
              | none => trivial
              | some fts =>
                rw [hf] at hv'
                intro p hp
                have _ : sizeOf p.2 < sizeOf (Value.construct qen ctor vs) := by
                  have := List.sizeOf_lt_of_mem (List.of_mem_zip hp).2
                  simp [Value.construct.sizeOf_spec]; omega
                exact ValOk.mono hext hle (hv' p hp)
            | field _ | tuple _ | ptr _ _ => trivial
  | b1, b2, .array t n, v, hle, hv => by
    unfold ValOk at hv ⊢
    by_cases hc : (t == u8Ty && n == 4) = true
    · simp only [hc, ↓reduceIte] at hv ⊢; exact hv
    · simp only [hc] at hv ⊢
      cases v with
      | tuple vs =>
        intro x hx
        have _ : sizeOf x < sizeOf (Value.tuple vs) := by
          have := List.sizeOf_lt_of_mem hx; simp [Value.tuple.sizeOf_spec]; omega
        exact ValOk.mono hext hle (hv x hx)
      | field _ | construct _ _ _ | ptr _ _ => trivial
  | b1, b2, .tuple ts, v, hle, hv => by
    unfold ValOk at hv ⊢
    cases v with
    | tuple vs =>
      intro p hp
      have _ : sizeOf p.2 < sizeOf (Value.tuple vs) := by
        have := List.sizeOf_lt_of_mem (List.of_mem_zip hp).2
        simp [Value.tuple.sizeOf_spec]; omega
      exact ValOk.mono hext hle (hv p hp)
    | field _ | construct _ _ _ | ptr _ _ => trivial
  | b1, b2, .ptr t, v, hle, hv => by
    unfold ValOk at hv ⊢
    cases v with
    | ptr pt addr =>
      obtain ⟨hlt, w, hget, hw⟩ := hv
      exact ⟨lt_of_lt_of_le hlt hle, w, hext.getElem?_eq hget, ValOk.mono hext (Nat.le_refl addr) hw⟩
    | field _ | tuple _ | construct _ _ _ => trivial
  | _, _, .field, _, _, _ | _, _, .param _, _, _, _ | _, _, .named _ (_ :: _), _, _, _ => by
    unfold ValOk; trivial
termination_by b1 _ _ v => (b1, sizeOf v)

theorem ValOk_of_isFieldOnlyTy {enums : List Aiur.Generic.EnumDecl} {h : Heap F} {b : Nat} :
    ∀ {t : Lower.Ty} (v : SourceValue F), isFieldOnlyTy t = true → ValOk enums h b t v
  | .field, _, _ => by simp
  | .array t n, v, hf => by
    simp only [isFieldOnlyTy] at hf
    have hne : (t == u8Ty && n == 4) = false := by
      cases t with
      | named nm ts => simp [isFieldOnlyTy] at hf
      | _ => simp [u8Ty]
    unfold ValOk
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    cases v with
    | tuple vs => intro x _; exact ValOk_of_isFieldOnlyTy x hf
    | _ => trivial
  | .tuple ts, v, hf => by
    simp only [isFieldOnlyTy] at hf
    unfold ValOk
    cases v with
    | tuple vs =>
      intro p hp
      have hmem : p.1 ∈ ts := (List.of_mem_zip hp).1
      have hfp1 : isFieldOnlyTy p.1 = true := by
        clear hp
        induction ts with
        | nil => cases hmem
        | cons a tl ih =>
          simp only [isFieldOnlyTy.isFieldOnlyTyList, Bool.and_eq_true] at hf
          rcases List.mem_cons.mp hmem with rfl | htl
          · exact hf.1
          · exact ih hf.2 htl
      have _ : sizeOf p.1 < sizeOf (Aiur.Generic.Ty.tuple ts) := by
        have := List.sizeOf_lt_of_mem hmem; simp [Aiur.Generic.Ty.tuple.sizeOf_spec]; omega
      exact ValOk_of_isFieldOnlyTy p.2 hfp1
    | _ => trivial
  | .param _, _, hf | .ptr _, _, hf | .named _ _, _, hf => by simp [isFieldOnlyTy] at hf
termination_by t _ _ => sizeOf t

theorem ValOk_array_elem {enums : List Aiur.Generic.EnumDecl} {h : Heap F} {b : Nat}
    {t : Lower.Ty} {n : Nat} {vs : List (SourceValue F)}
    (hv : ValOk enums h b (.array t n) (.tuple vs)) :
    ∀ x ∈ vs, ValOk enums h b t x := by
  unfold ValOk at hv
  split at hv
  · next hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨rfl, rfl⟩
    obtain ⟨_, b0, b1, b2, b3, h0, h1, h2, h3, _, heq⟩ := hv
    simp only [Value.tuple.injEq] at heq
    subst heq
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [ValOk_u8]; exact ⟨b0, h0, rfl⟩
    · simp [ValOk_u8]; exact ⟨b1, h1, rfl⟩
    · simp [ValOk_u8]; exact ⟨b2, h2, rfl⟩
    · simp [ValOk_u8]; exact ⟨b3, h3, rfl⟩
  · exact hv

theorem ValOk_array_of_elems {enums : List Aiur.Generic.EnumDecl} {h : Heap F} {b : Nat}
    {t : Lower.Ty} {n : Nat} {vs : List (SourceValue F)}
    (hlen : vs.length = n) (helems : ∀ x ∈ vs, ValOk enums h b t x) :
    ValOk enums h b (.array t n) (.tuple vs) := by
  unfold ValOk
  split
  · next hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨rfl, rfl⟩
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;> simp at hlen
    obtain ⟨b0, hb0, rfl⟩ := (ValOk_u8 enums h b v0).mp (helems _ (by simp))
    obtain ⟨b1, hb1, rfl⟩ := (ValOk_u8 enums h b v1).mp (helems _ (by simp))
    obtain ⟨b2, hb2, rfl⟩ := (ValOk_u8 enums h b v2).mp (helems _ (by simp))
    obtain ⟨b3, hb3, rfl⟩ := (ValOk_u8 enums h b v3).mp (helems _ (by simp))
    exact ⟨U32.pack b0 b1 b2 b3, b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩
  · exact helems

/-- Local environment typing invariant: every variable in `Γ` is bound in `locals`
with a valid value for its type. -/
def EnvOk (enums : List Aiur.Generic.EnumDecl) (h : Heap F) (b : Nat)
    (Γ : TyEnv) (locals : Environment F Nat) : Prop :=
  ∀ x t, Γ.lookup x = some t →
    ∃ v, locals.find? (·.1 == x) = some (x, v) ∧ ValOk enums h b t v

theorem EnvOk.mono {enums : List Aiur.Generic.EnumDecl} {h1 h2 : Heap F}
    (hext : Heap.Extends h1 h2) {b1 b2 : Nat} (hle : b1 ≤ b2)
    {Γ : TyEnv} {locals : Environment F Nat}
    (henv : EnvOk enums h1 b1 Γ locals) : EnvOk enums h2 b2 Γ locals := by
  intro x t hl
  obtain ⟨v, hv, hok⟩ := henv x t hl
  exact ⟨v, hv, hok.mono hext hle⟩

theorem envOk_zip {enums : List Aiur.Generic.EnumDecl} {h : Heap F} {b : Nat}
    {params : List (String × Lower.Ty)} {args : List (SourceValue F)}
    (hall : List.Forall₂ (ValOk enums h b) (params.map Prod.snd) args) :
    EnvOk enums h b params ((params.map Prod.fst).zip args) := by
  induction params generalizing args with
  | nil =>
    cases hall
    intro x t hl; simp at hl
  | cons hd tl ih =>
    cases args with
    | nil => cases hall
    | cons a rest =>
      cases hall with
      | cons hhd htl =>
        intro x t hl
        rcases hd with ⟨nm, ty⟩
        simp only [List.lookup, List.map_cons, List.zip_cons_cons, List.find?_cons] at hl ⊢
        by_cases hx : x = nm
        · subst hx
          simp only [beq_self_eq_true, Option.some.injEq] at hl ⊢
          subst hl
          exact ⟨a, rfl, hhd⟩
        · have hne1 : (x == nm) = false := beq_false_of_ne hx
          have hne2 : (nm == x) = false := beq_false_of_ne (Ne.symm hx)
          simp only [hne1] at hl
          simp only [hne2]
          exact ih htl x t hl

theorem envOk_append {enums : List Aiur.Generic.EnumDecl} {h : Heap F} {b : Nat}
    {Δ Γ : TyEnv} {bs locals : Environment F Nat}
    (h1 : List.Forall₂ (fun p d => p.1 = d.1 ∧ ValOk enums h b d.2 p.2) bs Δ)
    (h2 : EnvOk enums h b Γ locals) :
    EnvOk enums h b (Δ ++ Γ) (bs ++ locals) := by
  induction h1 with
  | nil => exact h2
  | @cons p d ps ds hd _ ih =>
    rcases p with ⟨nm, v⟩
    rcases d with ⟨nm', ty⟩
    rcases hd with ⟨hnm, hval⟩
    dsimp only at hnm hval
    subst hnm
    intro x t hl
    simp only [List.cons_append, List.lookup, List.find?_cons] at hl ⊢
    by_cases hx : x = nm
    · subst hx
      simp only [beq_self_eq_true, Option.some.injEq] at hl ⊢
      subst hl
      exact ⟨v, rfl, hval⟩
    · have hne1 : (x == nm) = false := beq_false_of_ne hx
      have hne2 : (nm == x) = false := beq_false_of_ne (Ne.symm hx)
      simp only [hne1] at hl
      simp only [hne2]
      exact ih x t hl

end ValOkDef

/-! ### Complete `UInt32` World Specification (`U32WorldSpec`) + Constructive Bridges -/

section U32Spec

variable {F : Type} [Field F] [DecidableEq F]

/-- Combined soundness + constructive forward-evaluation contract for all `UInt8`/`UInt32`
primitives used across `TypedLower`, `Peephole`, and `InlineFuse`.
Reuses `Peephole.U32Contracts` and `TypedGadgets.U32Contracts` directly! -/
structure U32WorldSpec (world : World F) : Prop where
  fc : FieldCompatible64 F
  peep : Peephole.U32Contracts world
  tg : TypedGadgets.U32Contracts world
  -- Soundness of remaining U32/U8 operations (for `ValOk` preservation & `isHeapPure`):
  from_fields_any : ∀ v h r h',
    EvalFn world "UInt32::from_fields" [v] h r h' →
    (∃ n, isU32Val n r) ∧ h' = h
  sub : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::sub" [wa, wb] h r h' →
    isU32Val ((U32.base + a - b) % U32.base) r ∧ h' = h
  and : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world "UInt32::and" [wa, wb] h r h' →
    isU32Val (a &&& b) r ∧ h' = h
  u32_of_field : ∀ v h r h',
    EvalFn world (qualified "u32_of_field") [v] h r h' →
    (∃ k : Nat, k < natLimit ∧ v = .field (k : F) ∧ isU32Val (k % U32.base) r) ∧ h' = h
  u32_mul : ∀ a b wa wb h r h', isU32Val a wa → isU32Val b wb →
    EvalFn world (qualified "u32_mul") [wa, wb] h r h' →
    isU32Val ((a * b) % U32.base) r ∧ h' = h
  u32_sub_borrow : ∀ (a b : Nat) h r h', a < U32.base → b < U32.base →
    EvalFn world "UInt32::sub_borrow" [.field (a : F), .field (b : F)] h r h' →
    (∃ w vf, r = .tuple [w, vf] ∧ ∃ n, isU32Val n w) ∧ h' = h
  u32_expand : ∀ (a : Nat) h r h', a < U32.base →
    EvalFn world "UInt32::expand" [.field (a : F)] h r h' →
    isU32Val a r ∧ h' = h
  u32_compact_from_field : ∀ v h r h',
    EvalFn world "UInt32::compact_from_field" [v] h r h' →
    (∃ n : Nat, n < U32.base ∧ r = .field (n : F)) ∧ h' = h
  u8_xor : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
    EvalFn world "UInt8::xor" [.field (a : F), .field (b : F)] h r h' →
    (∃ k : Nat, k < 256 ∧ r = .field (k : F)) ∧ h' = h
  u8_and : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
    EvalFn world "UInt8::and" [.field (a : F), .field (b : F)] h r h' →
    (∃ k : Nat, k < 256 ∧ r = .field (k : F)) ∧ h' = h
  u8_or : ∀ (a b : Nat) h r h', a < 256 → b < 256 →
    EvalFn world "UInt8::or" [.field (a : F), .field (b : F)] h r h' →
    (∃ k : Nat, k < 256 ∧ r = .field (k : F)) ∧ h' = h
  -- Constructive forward builders (for backward simulation of folds, fusions & cancellations):
  compact_mk : ∀ n w h, isU32Val n w →
    EvalFn world "UInt32::compact" [w] h (.field (n : F)) h
  compact_field_mk : ∀ v h,
    EvalFn world "UInt32::compact_field" [v] h v h
  from_fields_mk : ∀ n w h, isU32Val n w →
    EvalFn world "UInt32::from_fields" [w] h w h
  from_field_mk : ∀ n w h, isU32Val n w →
    EvalFn world "UInt32::from_field" [.field (n : F)] h w h
  u32_of_field_mk : ∀ n w h, n < natLimit → isU32Val (n % U32.base) w →
    EvalFn world (qualified "u32_of_field") [.field (n : F)] h w h
  add_mk : ∀ a b wa wb wr h, isU32Val a wa → isU32Val b wb → isU32Val ((a + b) % U32.base) wr →
    EvalFn world "UInt32::add" [wa, wb] h wr h
  sub_mk : ∀ a b wa wb wr h, isU32Val a wa → isU32Val b wb →
    isU32Val ((U32.base + a - b) % U32.base) wr →
    EvalFn world "UInt32::sub" [wa, wb] h wr h
  xor_mk : ∀ a b wa wb wr h, isU32Val a wa → isU32Val b wb → isU32Val (Nat.xor a b) wr →
    EvalFn world "UInt32::xor" [wa, wb] h wr h
  or_mk : ∀ a b wa wb wr h, isU32Val a wa → isU32Val b wb → isU32Val (a ||| b) wr →
    EvalFn world "UInt32::or" [wa, wb] h wr h
  shr_mk : ∀ a b wa wb wr h, isU32Val a wa → isU32Val b wb → isU32Val (a >>> (b % 32)) wr →
    EvalFn world (qualified "u32_shr") [wa, wb] h wr h
  shl_mk : ∀ a b wa wb wr h, isU32Val a wa → isU32Val b wb →
    isU32Val ((a <<< (b % 32)) % U32.base) wr →
    EvalFn world (qualified "u32_shl") [wa, wb] h wr h

/-- Constructive `UInt32::compact_field` bridge directly from its library body. -/
theorem evalFn_compact_field_mk {world : World F}
    (hprov : WorldProvidesFn world "UInt32::compact_field" ["word"] (.var "word"))
    (v : SourceValue F) (h : Heap F) :
    EvalFn world "UInt32::compact_field" [v] h v h :=
  .intro (hprov [v] rfl) (.var (by simp))

/-- Constructive `UInt32::compact` bridge directly from its library body. -/
theorem evalFn_compact_mk {world : World F}
    (hprov : WorldProvidesFn world "UInt32::compact" ["word"]
      (.binary .add
        (.binary .add
          (.binary .add
            (.call "UInt8::to_field" (some []) [.index (.var "word") 0])
            (.binary .mul (.literal ((256 : Nat) : F))
              (.call "UInt8::to_field" (some []) [.index (.var "word") 1])))
          (.binary .mul (.literal ((65536 : Nat) : F))
            (.call "UInt8::to_field" (some []) [.index (.var "word") 2])))
        (.binary .mul (.literal ((16777216 : Nat) : F))
          (.call "UInt8::to_field" (some []) [.index (.var "word") 3]))))
    (hu8 : ∀ b : Nat, b < 256 → ∀ h, EvalFn world "UInt8::to_field" [.field (b : F)] h (.field (b : F)) h)
    {n : Nat} {w : SourceValue F} (hw : isU32Val n w) (h : Heap F) :
    EvalFn world "UInt32::compact" [w] h (.field (n : F)) h := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, rfl⟩ := hw
  refine .intro (hprov _ rfl) ?_
  let tup : SourceValue F := .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]
  have hvar : EvalExpr world [] [("word", tup)] (.var "word") h tup h := .var (by simp)
  have mkByte : ∀ (idx bi : Nat), bi < 256 →
      ([.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)] :
        List (SourceValue F))[idx]? = some (.field (bi : F)) →
      EvalExpr world [] [("word", tup)]
        (.call "UInt8::to_field" (some []) [.index (.var "word") idx]) h (.field (bi : F)) h := by
    intro idx bi hbi hget
    refine .call (.cons (.index hvar (by simp [tup, projectValue, hget]; rfl)) .nil) ?_
    simpa [instanceName, Instance.symbol] using hu8 bi hbi h
  refine .binary (.binary (.binary (mkByte 0 b0 h0 (by simp))
    (.binary .literal (mkByte 1 b1 h1 (by simp)) (by simp [evalBinOp]; rfl))
    (by simp [evalBinOp]; rfl))
    (.binary .literal (mkByte 2 b2 h2 (by simp)) (by simp [evalBinOp]; rfl))
    (by simp [evalBinOp]; rfl))
    (.binary .literal (mkByte 3 b3 h3 (by simp)) (by simp [evalBinOp]; rfl)) ?_
  simp only [evalBinOp, U32.pack, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

omit [Field F] in
private theorem matchPattern_tuple_binds2 {world : World F} {h : Heap F}
    (x y : String) (vx vy : SourceValue F) :
    world.matchPattern [] h (.tuple [.bind x, .bind y]) (.tuple [vx, vy]) =
      .ok (some [(x, vx), (y, vy)]) := by
  simp only [World.matchPattern]
  rw [matchPatternWith]
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    matchListWith_attach, matchListWith, bind, Except.bind, pure, Except.pure]
  rw [matchPatternWith]
  simp only [pure, Except.pure]
  rw [matchPatternWith]
  simp only [pure, Except.pure, List.cons_append, List.nil_append]

omit [Field F] in
private theorem matchPattern_array_binds8 {world : World F} {h : Heap F}
    (n0 n1 n2 n3 n4 n5 n6 n7 : String) (v0 v1 v2 v3 v4 v5 v6 v7 : SourceValue F) :
    world.matchPattern [] h
      (.array [.bind n0, .bind n1, .bind n2, .bind n3, .bind n4, .bind n5, .bind n6, .bind n7])
      (.tuple [v0, v1, v2, v3, v4, v5, v6, v7]) =
      .ok (some [(n0, v0), (n1, v1), (n2, v2), (n3, v3), (n4, v4), (n5, v5), (n6, v6), (n7, v7)]) := by
  simp only [World.matchPattern]
  rw [matchPatternWith]
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    matchListWith_attach, matchListWith, bind, Except.bind, pure, Except.pure]
  repeat (rw [matchPatternWith]; simp only [pure, Except.pure, List.cons_append, List.nil_append])

/-- Constructive `UInt32::from_fields` bridge directly from its library body. -/
theorem evalFn_from_fields_mk {world : World F}
    (hprov : WorldProvidesFn world "UInt32::from_fields" ["raw"]
      (.letValue (.tuple [.bind "b0", .bind "b1"])
        (.call "UInt8::from_fields" (some []) [.index (.var "raw") 0, .index (.var "raw") 1])
        (.letValue (.tuple [.bind "b2", .bind "b3"])
          (.call "UInt8::from_fields" (some []) [.index (.var "raw") 2, .index (.var "raw") 3])
          (.array [.var "b0", .var "b1", .var "b2", .var "b3"]))))
    (hu8 : ∀ a b : Nat, a < 256 → b < 256 → ∀ h,
      EvalFn world "UInt8::from_fields" [.field (a : F), .field (b : F)] h
        (.tuple [.field (a : F), .field (b : F)]) h)
    {n : Nat} {w : SourceValue F} (hw : isU32Val n w) (h : Heap F) :
    EvalFn world "UInt32::from_fields" [w] h w h := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, rfl⟩ := hw
  refine .intro (hprov _ rfl) ?_
  let tup : SourceValue F := .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]
  have hraw0 : EvalExpr world [] [("raw", tup)] (.var "raw") h tup h := .var (by simp)
  refine .letValue (bindings := [("b0", .field (b0 : F)), ("b1", .field (b1 : F))])
    (.call (.cons (.index hraw0 (by simp [tup, projectValue]; rfl))
           (.cons (.index hraw0 (by simp [tup, projectValue]; rfl)) .nil))
      (by simpa [instanceName, Instance.symbol] using hu8 b0 b1 h0 h1 h))
    (matchPattern_tuple_binds2 "b0" "b1" _ _) ?_
  have hraw1 : EvalExpr world []
      ([("b0", .field (b0 : F)), ("b1", .field (b1 : F))] ++ [("raw", tup)])
      (.var "raw") h tup h := .var (by simp)
  refine .letValue (bindings := [("b2", .field (b2 : F)), ("b3", .field (b3 : F))])
    (.call (.cons (.index hraw1 (by simp [tup, projectValue]; rfl))
           (.cons (.index hraw1 (by simp [tup, projectValue]; rfl)) .nil))
      (by simpa [instanceName, Instance.symbol] using hu8 b2 b3 h2 h3 h))
    (matchPattern_tuple_binds2 "b2" "b3" _ _) ?_
  exact .array (.cons (.var (by simp)) (.cons (.var (by simp))
    (.cons (.var (by simp)) (.cons (.var (by simp)) .nil))))

/-- Constructive `UInt32::from_field` bridge directly from its library body. -/
theorem evalFn_from_field_mk {world : World F}
    (hprov : WorldProvidesFn world "UInt32::from_field" ["value"]
      (.letValue (.bind "raw") (.hint (.array .field 4) (.var "value") "u32.bytes")
        (.letValue (.bind "word") (.call "UInt32::from_fields" (some []) [.var "raw"])
          (.letValue .wildcard
            (.builtin (.assertEq { message := some "u32 decomposition" })
              [.call "UInt32::compact" (some []) [.var "word"], .var "value"])
            (.var "word")))))
    (htyped4 : ∀ b0 b1 b2 b3 : F,
      world.typed ((Aiur.Generic.Ty.array .field 4).subst []).toCore
        (.tuple [.field b0, .field b1, .field b2, .field b3]) = true)
    (hff : ∀ n w h, isU32Val n w → EvalFn world "UInt32::from_fields" [w] h w h)
    (hcmp : ∀ n w h, isU32Val n w → EvalFn world "UInt32::compact" [w] h (.field (n : F)) h)
    {n : Nat} {w : SourceValue F} (hw : isU32Val n w) (h : Heap F) :
    EvalFn world "UInt32::from_field" [.field (n : F)] h w h := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, rfl⟩ := hw
  have hw' : isU32Val (U32.pack b0 b1 b2 b3)
      (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]) :=
    ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, rfl⟩
  refine .intro (hprov _ rfl) ?_
  let wit : Constant F := Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]
  have hvalEq : (wit.toValue : SourceValue F) =
      Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)] := by
    simp [wit, Constant.toValue, Value.mapAddress]
  have hv0 : EvalExpr world [] (["value"].zip [Value.field ((U32.pack b0 b1 b2 b3 : Nat) : F)])
      (.var "value") h (Value.field ((U32.pack b0 b1 b2 b3 : Nat) : F)) h := .var (by simp)
  refine .letValue (bindings := [("raw", Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)])])
    (hvalEq ▸ EvalExpr.hint hv0 (htyped4 (b0 : F) (b1 : F) (b2 : F) (b3 : F)))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  refine .letValue (bindings := [("word", Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)])])
    (.call (.cons (.var (by simp; rfl)) .nil)
      (by simpa [instanceName, Instance.symbol] using hff _ _ h hw'))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  refine .letValue (bindings := [])
    (.builtin (.cons (.call (.cons (.var (by simp; rfl)) .nil)
      (by simpa [instanceName, Instance.symbol] using hcmp _ _ h hw'))
      (.cons (.var (by simp; rfl)) .nil))
      (by simp [Builtin.apply, evalAssertEq, Value.pointerFree]; rfl))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  exact .var (by simp)

private theorem body_u32OfFieldFn :
    u32OfFieldFn.body =
      .letValue (.array [.bind "h0", .bind "h1", .bind "h2", .bind "h3",
                         .bind "h4", .bind "h5", .bind "h6", .bind "h7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue (.bind "lo")
          (.call "UInt32::from_fields" (some []) [.array [.var "h0", .var "h1", .var "h2", .var "h3"]])
          (.letValue (.bind "hi")
            (.call "UInt32::from_fields" (some []) [.array [.var "h4", .var "h5", .var "h6", .var "h7"]])
            (.letValue .wildcard
              (.builtin (.assertEq (Lower.assertion "u32_of_field: top byte zero")) [.var "h7", .literal 0])
              (.letValue .wildcard
                (.builtin (.assertEq (Lower.assertion "u32_of_field: recomposition"))
                  [.binary .add
                    (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "lo"]])
                    (.binary .mul (.literal (2 ^ 32))
                      (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "hi"]])),
                   .var "x"])
                (.var "lo"))))) := rfl

/-- Constructive `Prog::u32_of_field` bridge directly from `TypedLower.u32OfFieldFn`:
for any `n < 2^56` and checked 4-byte `w` packing `n % 2^32`, builds a complete
`EvalFn` derivation of `Prog::u32_of_field [.field (n : F)]` returning `w` with unchanged heap! -/
theorem evalFn_u32_of_field_mk {world : World F}
    (hprov : WorldProvidesFn world (qualified "u32_of_field") ["x"]
      (qualifyExprF F u32OfFieldFn.body))
    (htyped8 : ∀ c0 c1 c2 c3 c4 c5 c6 c7 : F,
      world.typed ((Aiur.Generic.Ty.array .field 8).subst []).toCore
        (.tuple [.field c0, .field c1, .field c2, .field c3,
                 .field c4, .field c5, .field c6, .field c7]) = true)
    (hff : ∀ k w h, isU32Val k w → EvalFn world "UInt32::from_fields" [w] h w h)
    (hcmp : ∀ k w h, isU32Val k w → EvalFn world "UInt32::compact" [w] h (.field (k : F)) h)
    (hcf : ∀ v h, EvalFn world "UInt32::compact_field" [v] h v h)
    {n : Nat} (hn : n < natLimit) {w : SourceValue F} (hw : isU32Val (n % U32.base) w)
    (h : Heap F) :
    EvalFn world (qualified "u32_of_field") [.field (n : F)] h w h := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, hloPack, rfl⟩ := hw
  set hi := n / U32.base
  have hhiLt : hi < 2 ^ 24 := by unfold hi U32.base natLimit at *; omega
  set b4 := hi % 256
  set b5 := (hi / 256) % 256
  set b6 := (hi / 65536) % 256
  have h4 : b4 < 256 := Nat.mod_lt _ (by omega)
  have h5 : b5 < 256 := Nat.mod_lt _ (by omega)
  have h6 : b6 < 256 := Nat.mod_lt _ (by omega)
  have hhiPack : hi = U32.pack b4 b5 b6 0 := by
    have hdiv : hi / 256 / 256 = hi / 65536 := by rw [Nat.div_div_eq_div_mul]
    have h6eq : b6 = hi / 65536 := Nat.mod_eq_of_lt (by omega)
    unfold b4 b5 U32.pack
    omega
  have hrecomp : U32.pack b0 b1 b2 b3 + 2 ^ 32 * U32.pack b4 b5 b6 0 = n := by
    rw [← hloPack, ← hhiPack]; unfold hi U32.base; omega
  have hloVal : isU32Val (U32.pack b0 b1 b2 b3)
      (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]) :=
    ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, rfl⟩
  have hhiVal : isU32Val (U32.pack b4 b5 b6 0)
      (.tuple [.field (b4 : F), .field (b5 : F), .field (b6 : F), .field ((0 : Nat) : F)]) :=
    ⟨b4, b5, b6, 0, h4, h5, h6, by omega, rfl, rfl⟩
  refine .intro (hprov _ rfl) ?_
  rw [body_u32OfFieldFn]
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy,
    TypedGadgets.qualifyName_u32_from_fields,
    TypedGadgets.qualifyName_u32_compact_field,
    TypedGadgets.qualifyName_u32_compact,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map]
  let wit : Constant F := Value.tuple
    [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
     .field (b4 : F), .field (b5 : F), .field (b6 : F), .field ((0 : Nat) : F)]
  have hvalEq : (wit.toValue : SourceValue F) =
      Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
                   .field (b4 : F), .field (b5 : F), .field (b6 : F), .field ((0 : Nat) : F)] := by
    simp [wit, Constant.toValue, Value.mapAddress]
  have hv0 : EvalExpr world [] (["x"].zip [Value.field (n : F)])
      (.var "x") h (Value.field (n : F)) h := .var (by simp)
  refine .letValue (bindings :=
      [("h0", .field (b0 : F)), ("h1", .field (b1 : F)), ("h2", .field (b2 : F)), ("h3", .field (b3 : F)),
       ("h4", .field (b4 : F)), ("h5", .field (b5 : F)), ("h6", .field (b6 : F)), ("h7", .field ((0 : Nat) : F))])
    (hvalEq ▸ EvalExpr.hint hv0
      (htyped8 (b0 : F) (b1 : F) (b2 : F) (b3 : F) (b4 : F) (b5 : F) (b6 : F) ((0 : Nat) : F)))
    (matchPattern_array_binds8 "h0" "h1" "h2" "h3" "h4" "h5" "h6" "h7" _ _ _ _ _ _ _ _) ?_
  refine .letValue (bindings := [("lo", .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)])])
    (.call (.cons (.array (.cons (.var (by simp; rfl)) (.cons (.var (by simp; rfl))
      (.cons (.var (by simp; rfl)) (.cons (.var (by simp; rfl)) .nil))))) .nil)
      (by simpa [instanceName, Instance.symbol] using hff _ _ h hloVal))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  refine .letValue (bindings := [("hi", .tuple [.field (b4 : F), .field (b5 : F), .field (b6 : F), .field ((0 : Nat) : F)])])
    (.call (.cons (.array (.cons (.var (by simp; rfl)) (.cons (.var (by simp; rfl))
      (.cons (.var (by simp; rfl)) (.cons (.var (by simp; rfl)) .nil))))) .nil)
      (by simpa [instanceName, Instance.symbol] using hff _ _ h hhiVal))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  refine .letValue (bindings := [])
    (.builtin (.cons (.var (by simp; rfl)) (.cons .literal .nil))
      (by simp [Builtin.apply, evalAssertEq, Value.pointerFree]; rfl))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  have hcast : ((U32.pack b0 b1 b2 b3 : Nat) : F) +
      ((4294967296 : Nat) : F) * ((U32.pack b4 b5 b6 0 : Nat) : F) = (n : F) := by
    rw [← Nat.cast_mul, ← Nat.cast_add]; exact congrArg Nat.cast hrecomp
  have hcast' : ((U32.pack b0 b1 b2 b3 : Nat) : F) +
      (4294967296 : F) * ((U32.pack b4 b5 b6 0 : Nat) : F) = (n : F) := by
    simpa only [Nat.cast_ofNat] using hcast
  refine .letValue (bindings := [])
    (.builtin (.cons
      (.binary
        (.call (.cons (.call (.cons (.var (by simp; rfl)) .nil)
          (by simpa [instanceName, Instance.symbol] using hcmp _ _ h hloVal)) .nil)
          (by simpa [instanceName, Instance.symbol] using hcf _ h))
        (.binary .literal
          (.call (.cons (.call (.cons (.var (by simp; rfl)) .nil)
            (by simpa [instanceName, Instance.symbol] using hcmp _ _ h hhiVal)) .nil)
            (by simpa [instanceName, Instance.symbol] using hcf _ h))
          (by simp [evalBinOp]; rfl))
        (by simp [evalBinOp]; rfl))
      (.cons (.var (by simp; rfl)) .nil))
      (by simp [Builtin.apply, evalAssertEq, Value.pointerFree, hcast']; rfl))
    (by simp [World.matchPattern, matchPatternWith]) ?_
  exact .var (by simp)

/-- Standard-library self-containment: any evaluation of a non-`"Prog::"` function
transfers between worlds agreeing with `w0` on auxiliary tables and non-`"Prog::"`
definitions. -/
def LibSelfContained (w0 : World F) : Prop :=
  ∀ (w1 w2 : World F) (nm : String) (args : List (SourceValue F)) (h h' : Heap F) (r : SourceValue F),
    SameAuxWorld w1 w0 → SameAuxWorld w2 w0 →
    (∀ m a, isProgQName m = false → w1.prepare m a = w0.prepare m a) →
    (∀ m a, isProgQName m = false → w2.prepare m a = w0.prepare m a) →
    isProgQName nm = false →
    EvalFn w1 nm args h r h' → EvalFn w2 nm args h r h'

mutual

/-- Syntactic predicate: `e` contains no calls to inlinable user functions (`f*` / `jp*`). -/
def noInlinableCalls : Expr → Bool
  | .call nm _ xs =>
    !(nm.startsWith "f" || nm.startsWith "jp") && noInlinableCallsList xs
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => noInlinableCallsList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x => noInlinableCalls x
  | .binary _ l r => noInlinableCalls l && noInlinableCalls r
  | .letValue _ v b => noInlinableCalls v && noInlinableCalls b
  | .matchValue s arms => noInlinableCalls s && noInlinableCallsArms arms
  | .literal _ | .var _ | .global _ _ => true

def noInlinableCallsList : List Expr → Bool
  | [] => true
  | x :: xs => noInlinableCalls x && noInlinableCallsList xs

def noInlinableCallsArms : List (Pat × Expr) → Bool
  | [] => true
  | (_, b) :: rest => noInlinableCalls b && noInlinableCallsArms rest

end

/-- An arithmetic helper function whose body has no calls to inlinable `f*`/`jp*` functions
and is already a fixpoint of `simpExpr 16` and `simpExpr 32`. -/
def IsFixedHelper (f : Fn) : Prop :=
  noInlinableCalls f.body = true ∧
  simpExpr 16 [] [] [] f.body = f.body ∧
  simpExpr 32 [] [] [] f.body = f.body

/-- Arithmetic-helper self-containment: evaluations of `Prog::u32_of_field`, `Prog::u32_shr`,
`Prog::u32_shl`, and `Prog::u32_mul` transfer between worlds agreeing with `w0` on auxiliary
tables, non-`"Prog::"` definitions, and all `IsFixedHelper` functions in `fns`. -/
def HelpersSelfContained (w0 : World F) (fns : List Fn) : Prop :=
  ∀ (w1 w2 : World F) (nm : String) (args : List (SourceValue F)) (h h' : Heap F) (r : SourceValue F),
    SameAuxWorld w1 w0 → SameAuxWorld w2 w0 →
    (∀ m a, isProgQName m = false → w1.prepare m a = w0.prepare m a) →
    (∀ m a, isProgQName m = false → w2.prepare m a = w0.prepare m a) →
    (∀ f ∈ fns, IsFixedHelper f → ∀ a, w1.prepare (qualified f.name) a = w0.prepare (qualified f.name) a) →
    (∀ f ∈ fns, IsFixedHelper f → ∀ a, w2.prepare (qualified f.name) a = w0.prepare (qualified f.name) a) →
    (nm = qualified "u32_of_field" ∨ nm = qualified "u32_shr" ∨
     nm = qualified "u32_shl" ∨ nm = qualified "u32_mul") →
    EvalFn w1 nm args h r h' → EvalFn w2 nm args h r h'

/-- Transfer `U32WorldSpec` from `w0` to any world `w'` agreeing with `w0` on auxiliary tables,
non-`"Prog::"` definitions, and `IsFixedHelper` functions in `fns`. -/
theorem U32WorldSpec.transfer {w0 w' : World F} {fns : List Fn}
    (spec : U32WorldSpec w0)
    (hLib : LibSelfContained w0)
    (hHelp : HelpersSelfContained w0 fns)
    (haux : SameAuxWorld w' w0)
    (hNonProg : ∀ m a, isProgQName m = false → w'.prepare m a = w0.prepare m a)
    (hFixed : ∀ f ∈ fns, IsFixedHelper f → ∀ a, w'.prepare (qualified f.name) a = w0.prepare (qualified f.name) a) :
    U32WorldSpec w' := by
  have toW0 : ∀ nm args h r h', isProgQName nm = false → EvalFn w' nm args h r h' → EvalFn w0 nm args h r h' :=
    fun nm args h r h' hnp ev => hLib w' w0 nm args h h' r haux (.refl w0) hNonProg (fun _ _ _ => rfl) hnp ev
  have toW' : ∀ nm args h r h', isProgQName nm = false → EvalFn w0 nm args h r h' → EvalFn w' nm args h r h' :=
    fun nm args h r h' hnp ev => hLib w0 w' nm args h h' r (.refl w0) haux (fun _ _ _ => rfl) hNonProg hnp ev
  have hToW0 : ∀ nm args h r h',
      (nm = qualified "u32_of_field" ∨ nm = qualified "u32_shr" ∨
       nm = qualified "u32_shl" ∨ nm = qualified "u32_mul") →
      EvalFn w' nm args h r h' → EvalFn w0 nm args h r h' :=
    fun nm args h r h' hnm ev =>
      hHelp w' w0 nm args h h' r haux (.refl w0) hNonProg (fun _ _ _ => rfl) hFixed (fun _ _ _ _ => rfl) hnm ev
  have hToW' : ∀ nm args h r h',
      (nm = qualified "u32_of_field" ∨ nm = qualified "u32_shr" ∨
       nm = qualified "u32_shl" ∨ nm = qualified "u32_mul") →
      EvalFn w0 nm args h r h' → EvalFn w' nm args h r h' :=
    fun nm args h r h' hnm ev =>
      hHelp w0 w' nm args h h' r (.refl w0) haux (fun _ _ _ => rfl) hNonProg (fun _ _ _ _ => rfl) hFixed hnm ev
  refine
    { fc := spec.fc
      peep :=
        { add := fun a b wa wb h r h' ha hb ev => spec.peep.add a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
          add3 := fun a b c wa wb wc h r h' ha hb hc ev => spec.peep.add3 a b c wa wb wc h r h' ha hb hc (toW0 _ _ _ _ _ rfl ev)
          xor := fun a b wa wb h r h' ha hb ev => spec.peep.xor a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
          or := fun a b wa wb h r h' ha hb ev => spec.peep.or a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
          rotr8 := fun a wa h r h' ha ev => spec.peep.rotr8 a wa h r h' ha (toW0 _ _ _ _ _ rfl ev)
          rotr16 := fun a wa h r h' ha ev => spec.peep.rotr16 a wa h r h' ha (toW0 _ _ _ _ _ rfl ev)
          xor_rotr7 := fun a b wa wb h r h' ha hb ev => spec.peep.xor_rotr7 a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
          xor_rotr12 := fun a b wa wb h r h' ha hb ev => spec.peep.xor_rotr12 a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
          to_bytes := fun a wa h r h' ha ev => spec.peep.to_bytes a wa h r h' ha (toW0 _ _ _ _ _ rfl ev)
          from_bytes := fun a wa h r h' ha ev => spec.peep.from_bytes a wa h r h' ha (toW0 _ _ _ _ _ rfl ev)
          u8_from_fields := fun v1 v2 h r h' ev => spec.peep.u8_from_fields v1 v2 h r h' (toW0 _ _ _ _ _ rfl ev)
          shr := fun a b wa wb h r h' ha hb ev => spec.peep.shr a b wa wb h r h' ha hb (hToW0 _ _ _ _ _ (Or.inr (Or.inl rfl)) ev)
          shl := fun a b wa wb h r h' ha hb ev => spec.peep.shl a b wa wb h r h' ha hb (hToW0 _ _ _ _ _ (Or.inr (Or.inr (Or.inl rfl))) ev) }
      tg :=
        { compact := fun a wa h r h' ha ev => spec.tg.compact a wa h r h' ha (toW0 _ _ _ _ _ rfl ev)
          compact_field := fun v h r h' ev => spec.tg.compact_field v h r h' (toW0 _ _ _ _ _ rfl ev)
          from_fields := fun b0 b1 b2 b3 h r h' ev => spec.tg.from_fields b0 b1 b2 b3 h r h' (toW0 _ _ _ _ _ rfl ev)
          from_field := fun v h r h' ev => spec.tg.from_field v h r h' (toW0 _ _ _ _ _ rfl ev)
          to_bytes := fun a wa h r h' ha ev => spec.tg.to_bytes a wa h r h' ha (toW0 _ _ _ _ _ rfl ev)
          u8_to_field := fun b h r h' ev => spec.tg.u8_to_field b h r h' (toW0 _ _ _ _ _ rfl ev) }
      from_fields_any := fun v h r h' ev => spec.from_fields_any v h r h' (toW0 _ _ _ _ _ rfl ev)
      sub := fun a b wa wb h r h' ha hb ev => spec.sub a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
      and := fun a b wa wb h r h' ha hb ev => spec.and a b wa wb h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
      u32_of_field := fun v h r h' ev => spec.u32_of_field v h r h' (hToW0 _ _ _ _ _ (Or.inl rfl) ev)
      u32_mul := fun a b wa wb h r h' ha hb ev => spec.u32_mul a b wa wb h r h' ha hb (hToW0 _ _ _ _ _ (Or.inr (Or.inr (Or.inr rfl))) ev)
      u32_sub_borrow := fun a b h r h' ha hb ev => spec.u32_sub_borrow a b h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
      u32_expand := fun a h r h' ha ev => spec.u32_expand a h r h' ha (toW0 _ _ _ _ _ rfl ev)
      u32_compact_from_field := fun v h r h' ev => spec.u32_compact_from_field v h r h' (toW0 _ _ _ _ _ rfl ev)
      u8_xor := fun a b h r h' ha hb ev => spec.u8_xor a b h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
      u8_and := fun a b h r h' ha hb ev => spec.u8_and a b h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
      u8_or := fun a b h r h' ha hb ev => spec.u8_or a b h r h' ha hb (toW0 _ _ _ _ _ rfl ev)
      compact_mk := fun n w h hw => toW' _ _ _ _ _ rfl (spec.compact_mk n w h hw)
      compact_field_mk := fun v h => toW' _ _ _ _ _ rfl (spec.compact_field_mk v h)
      from_fields_mk := fun n w h hw => toW' _ _ _ _ _ rfl (spec.from_fields_mk n w h hw)
      from_field_mk := fun n w h hw => toW' _ _ _ _ _ rfl (spec.from_field_mk n w h hw)
      u32_of_field_mk := fun n w h hn hw => hToW' _ _ _ _ _ (Or.inl rfl) (spec.u32_of_field_mk n w h hn hw)
      add_mk := fun a b wa wb wr h ha hb hr => toW' _ _ _ _ _ rfl (spec.add_mk a b wa wb wr h ha hb hr)
      sub_mk := fun a b wa wb wr h ha hb hr => toW' _ _ _ _ _ rfl (spec.sub_mk a b wa wb wr h ha hb hr)
      xor_mk := fun a b wa wb wr h ha hb hr => toW' _ _ _ _ _ rfl (spec.xor_mk a b wa wb wr h ha hb hr)
      or_mk := fun a b wa wb wr h ha hb hr => toW' _ _ _ _ _ rfl (spec.or_mk a b wa wb wr h ha hb hr)
      shr_mk := fun a b wa wb wr h ha hb hr => hToW' _ _ _ _ _ (Or.inr (Or.inl rfl)) (spec.shr_mk a b wa wb wr h ha hb hr)
      shl_mk := fun a b wa wb wr h ha hb hr => hToW' _ _ _ _ _ (Or.inr (Or.inr (Or.inl rfl))) (spec.shl_mk a b wa wb wr h ha hb hr) }

end U32Spec

/-! ### Typing Judgment (`PatHasTy`, `HasTy`, `ProgWellTyped`) & Soundness (`evalExpr_valOk`) -/

section HasTyDef

mutual

/-- Typing judgment for simple patterns: `PatHasTy enums p t Δ` checks `p` against `t`
and produces the ordered list of newly bound variable types `Δ`. -/
inductive PatHasTy (enums : List Aiur.Generic.EnumDecl) : Pat → Lower.Ty → TyEnv → Prop where
  | wildcard {t : Lower.Ty} : PatHasTy enums .wildcard t []
  | literal {n : Nat} : PatHasTy enums (.literal n) .field []
  | bind {x : String} {t : Lower.Ty} : PatHasTy enums (.bind x) t [(x, t)]
  | tuple {ps : List Pat} {ts : List Lower.Ty} {Δ : TyEnv}
      (items : PatListHasTy enums ps ts Δ) :
      PatHasTy enums (.tuple ps) (.tuple ts) Δ
  | array {ps : List Pat} {t : Lower.Ty} {n : Nat} {Δ : TyEnv}
      (items : PatListHasTy enums ps (List.replicate ps.length t) Δ) :
      PatHasTy enums (.array ps) (.array t n) Δ
  | construct {en ctor : String} {ps : List Pat} {fts : List Lower.Ty} {Δ : TyEnv}
      (hne4 : en ≠ "UInt64::U64")
      (hctor : findCtorFields enums en ctor = some fts)
      (items : PatListHasTy enums ps fts Δ) :
      PatHasTy enums (.construct (.named en []) ctor ps) (.named en []) Δ

inductive PatListHasTy (enums : List Aiur.Generic.EnumDecl) :
    List Pat → List Lower.Ty → TyEnv → Prop where
  | nil : PatListHasTy enums [] [] []
  | cons {p : Pat} {t : Lower.Ty} {Δ1 : TyEnv} {ps : List Pat} {ts : List Lower.Ty} {Δ2 : TyEnv}
      (hd : PatHasTy enums p t Δ1)
      (tl : PatListHasTy enums ps ts Δ2) :
      PatListHasTy enums (p :: ps) (t :: ts) (Δ1 ++ Δ2)

end

mutual

theorem PatHasTy.isSimple {enums : List Aiur.Generic.EnumDecl} :
    ∀ {p : Pat} {t : Lower.Ty} {Δ : TyEnv}, PatHasTy enums p t Δ → isSimplePat p = true
  | _, _, _, .wildcard => rfl
  | _, _, _, .literal => rfl
  | _, _, _, .bind => rfl
  | _, _, _, .tuple items => items.isSimple
  | _, _, _, .array items => items.isSimple
  | _, _, _, .construct _ _ items => items.isSimple

theorem PatListHasTy.isSimple {enums : List Aiur.Generic.EnumDecl} :
    ∀ {ps : List Pat} {ts : List Lower.Ty} {Δ : TyEnv}, PatListHasTy enums ps ts Δ → isSimplePatList ps = true
  | _, _, _, .nil => rfl
  | _, _, _, .cons hd tl => by simp [isSimplePatList, hd.isSimple, tl.isSimple]

end

mutual

theorem PatHasTy.dom_eq {enums : List Aiur.Generic.EnumDecl} :
    ∀ {p : Pat} {t : Lower.Ty} {Δ : TyEnv}, PatHasTy enums p t Δ → Δ.map Prod.fst = patBoundVars p
  | _, _, _, .wildcard => rfl
  | _, _, _, .literal => rfl
  | _, _, _, .bind => rfl
  | _, _, _, .tuple items => items.dom_eq
  | _, _, _, .array items => items.dom_eq
  | _, _, _, .construct _ _ items => items.dom_eq

theorem PatListHasTy.dom_eq {enums : List Aiur.Generic.EnumDecl} :
    ∀ {ps : List Pat} {ts : List Lower.Ty} {Δ : TyEnv},
      PatListHasTy enums ps ts Δ → Δ.map Prod.fst = patListBoundVars ps
  | _, _, _, .nil => rfl
  | _, _, _, .cons hd tl => by simp [patListBoundVars, hd.dom_eq, tl.dom_eq]

end

mutual

/-- Sound typing judgment for plain `TypedLower` / `InlineFuse` / `Peephole` expressions. -/
inductive HasTy (sigs : FnSigs) (enums : List Aiur.Generic.EnumDecl) :
    TyEnv → Expr → Lower.Ty → Prop where
  | literal {Γ : TyEnv} {n : Nat} : HasTy sigs enums Γ (.literal n) .field
  | var {Γ : TyEnv} {x : String} {t : Lower.Ty} (hl : Γ.lookup x = some t) :
      HasTy sigs enums Γ (.var x) t
  | tuple {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty}
      (items : HasTyList sigs enums Γ xs ts) :
      HasTy sigs enums Γ (.tuple xs) (.tuple ts)
  | array {Γ : TyEnv} {xs : List Expr} {t : Lower.Ty} {n : Nat}
      (hlen : xs.length = n)
      (items : HasTyList sigs enums Γ xs (List.replicate n t)) :
      HasTy sigs enums Γ (.array xs) (.array t n)
  | «repeat» {Γ : TyEnv} {x : Expr} {t : Lower.Ty} {n : Nat}
      (hx : HasTy sigs enums Γ x t) :
      HasTy sigs enums Γ (.repeat x n) (.array t n)
  | index {Γ : TyEnv} {x : Expr} {t : Lower.Ty} {n i : Nat}
      (hx : HasTy sigs enums Γ x (.array t n)) :
      HasTy sigs enums Γ (.index x i) t
  | project {Γ : TyEnv} {x : Expr} {ts : List Lower.Ty} {i : Nat} {ti : Lower.Ty}
      (hx : HasTy sigs enums Γ x (.tuple ts))
      (hget : ts[i]? = some ti) :
      HasTy sigs enums Γ (.project x i) ti
  | slice {Γ : TyEnv} {x : Expr} {t : Lower.Ty} {n m a : Nat} {b : Option Nat}
      (hnot : t ≠ u8Ty)
      (hx : HasTy sigs enums Γ x (.array t n)) :
      HasTy sigs enums Γ (.slice x a b) (.array t m)
  | construct {Γ : TyEnv} {en ctor : String} {xs : List Expr} {fts : List Lower.Ty}
      (hne1 : en ≠ "UInt32::U32") (hne2 : en ≠ "UInt32::Compact")
      (hne3 : en ≠ "UInt8::U8") (hne4 : en ≠ "UInt64::U64")
      (hctor : findCtorFields enums en ctor = some fts)
      (items : HasTyList sigs enums Γ xs fts) :
      HasTy sigs enums Γ (.construct en (some []) ctor xs) (.named en [])
  | builtin {Γ : TyEnv} {op : Builtin} {xs : List Expr} {ts : List Lower.Ty}
      (items : HasTyList sigs enums Γ xs ts) :
      HasTy sigs enums Γ (.builtin op xs) (.tuple [])
  | store {Γ : TyEnv} {x : Expr} {t : Lower.Ty}
      (hx : HasTy sigs enums Γ x t) :
      HasTy sigs enums Γ (.store x) (.ptr t)
  | load {Γ : TyEnv} {x : Expr} {t : Lower.Ty}
      (hx : HasTy sigs enums Γ x (.ptr t)) :
      HasTy sigs enums Γ (.load x) t
  | hint {Γ : TyEnv} {t tx : Lower.Ty} {x : Expr} {ch : String}
      (hfo : isFieldOnlyTy t = true)
      (hx : HasTy sigs enums Γ x tx) :
      HasTy sigs enums Γ (.hint t x ch) t
  | neg {Γ : TyEnv} {x : Expr}
      (hx : HasTy sigs enums Γ x .field) :
      HasTy sigs enums Γ (.neg x) .field
  | binary {Γ : TyEnv} {op : BinOp} {l r : Expr}
      (hl : HasTy sigs enums Γ l .field)
      (hr : HasTy sigs enums Γ r .field) :
      HasTy sigs enums Γ (.binary op l r) .field
  | call {Γ : TyEnv} {nm : String} {xs : List Expr} {ptys : List Lower.Ty} {rty : Lower.Ty}
      (hsig : sigs (qualifyName nm) = some (ptys, rty))
      (items : HasTyList sigs enums Γ xs ptys) :
      HasTy sigs enums Γ (.call nm (some []) xs) rty
  | letValue {Γ : TyEnv} {p : Pat} {x b : Expr} {tx tb : Lower.Ty} {Δ : TyEnv}
      (hx : HasTy sigs enums Γ x tx)
      (hp : PatHasTy enums p tx Δ)
      (hb : HasTy sigs enums (Δ ++ Γ) b tb) :
      HasTy sigs enums Γ (.letValue p x b) tb
  | matchValue {Γ : TyEnv} {s : Expr} {arms : List (Pat × Expr)} {ts tb : Lower.Ty}
      (hs : HasTy sigs enums Γ s ts)
      (harms : HasTyArms sigs enums Γ ts arms tb) :
      HasTy sigs enums Γ (.matchValue s arms) tb

inductive HasTyList (sigs : FnSigs) (enums : List Aiur.Generic.EnumDecl) :
    TyEnv → List Expr → List Lower.Ty → Prop where
  | nil {Γ : TyEnv} : HasTyList sigs enums Γ [] []
  | cons {Γ : TyEnv} {x : Expr} {t : Lower.Ty} {xs : List Expr} {ts : List Lower.Ty}
      (hd : HasTy sigs enums Γ x t)
      (tl : HasTyList sigs enums Γ xs ts) :
      HasTyList sigs enums Γ (x :: xs) (t :: ts)

inductive HasTyArms (sigs : FnSigs) (enums : List Aiur.Generic.EnumDecl) :
    TyEnv → Lower.Ty → List (Pat × Expr) → Lower.Ty → Prop where
  | nil {Γ : TyEnv} {ts tb : Lower.Ty} : HasTyArms sigs enums Γ ts [] tb
  | cons {Γ : TyEnv} {p : Pat} {b : Expr} {rest : List (Pat × Expr)}
      {ts tb : Lower.Ty} {Δ : TyEnv}
      (hp : PatHasTy enums p ts Δ)
      (hb : HasTy sigs enums (Δ ++ Γ) b tb)
      (tl : HasTyArms sigs enums Γ ts rest tb) :
      HasTyArms sigs enums Γ ts ((p, b) :: rest) tb

end

mutual

theorem HasTy.isClean {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty}, HasTy sigs enums Γ e t → isCleanExpr e = true
  | _, _, _, .literal | _, _, _, .var _ => rfl
  | _, _, _, .tuple items | _, _, _, .array _ items | _, _, _, .construct _ _ _ _ _ items
  | _, _, _, .builtin items | _, _, _, .call _ items => items.isClean
  | _, _, _, .repeat hx | _, _, _, .index hx | _, _, _, .project hx _
  | _, _, _, .slice _ hx | _, _, _, .store hx | _, _, _, .load hx
  | _, _, _, .hint _ hx | _, _, _, .neg hx => hx.isClean
  | _, _, _, .binary hl hr => by simp [isCleanExpr, hl.isClean, hr.isClean]
  | _, _, _, .letValue hx hp hb => by simp [isCleanExpr, hp.isSimple, hx.isClean, hb.isClean]
  | _, _, _, .matchValue hs harms => by simp [isCleanExpr, hs.isClean, harms.isClean]

theorem HasTyList.isClean {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty}, HasTyList sigs enums Γ xs ts → isCleanList xs = true
  | _, _, _, .nil => rfl
  | _, _, _, .cons hd tl => by simp [isCleanList, hd.isClean, tl.isClean]

theorem HasTyArms.isClean {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {ts : Lower.Ty} {arms : List (Pat × Expr)} {tb : Lower.Ty},
      HasTyArms sigs enums Γ ts arms tb → isCleanArms arms = true
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons hp hb tl => by simp [isCleanArms, hp.isSimple, hb.isClean, tl.isClean]

end

theorem HasTy.isPlain {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {e : Expr} {t : Lower.Ty} (h : HasTy sigs enums Γ e t) :
    isPlainExpr e = true :=
  isPlainExpr_of_isCleanExpr h.isClean

theorem HasTyList.length_eq {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList sigs enums Γ xs ts → xs.length = ts.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ tl => congrArg Nat.succ tl.length_eq

theorem HasTyArms.mem {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {ts tb : Lower.Ty} :
    ∀ {arms : List (Pat × Expr)} {p : Pat} {b : Expr},
      HasTyArms sigs enums Γ ts arms tb → (p, b) ∈ arms →
      ∃ Δ, PatHasTy enums p ts Δ ∧ HasTy sigs enums (Δ ++ Γ) b tb
  | _, _, _, .nil, hmem => by cases hmem
  | _, _, _, .cons hp hb tl, hmem => by
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨_, hp, hb⟩
    · exact tl.mem htl

theorem lookup_append_agree {Δ Γ1 Γ2 : TyEnv} {x : String}
    (h : x ∉ Δ.map Prod.fst → Γ1.lookup x = Γ2.lookup x) :
    (Δ ++ Γ1).lookup x = (Δ ++ Γ2).lookup x := by
  induction Δ with
  | nil => exact h (by simp)
  | cons hd tl ih =>
    rcases hd with ⟨nm, ty⟩
    simp only [List.cons_append, List.lookup]
    by_cases hx : x = nm
    · subst hx; simp
    · simp only [beq_false_of_ne hx]
      exact ih fun hnot => h (by simp [hx, hnot])

mutual

/-- Typing environment congruence: if `Γ1` and `Γ2` agree on all free variables of `e`,
then `HasTy sigs enums Γ1 e t` transfers to `Γ2`. -/
theorem hasTy_envAgree {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ1 Γ2 : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy sigs enums Γ1 e t →
      (∀ x, hasFreeVar x e = true → Γ1.lookup x = Γ2.lookup x) →
      HasTy sigs enums Γ2 e t
  | _, _, _, _, .literal, _ => .literal
  | _, _, _, _, .var hl, hag => .var (by rw [← hag _ (by simp [hasFreeVar])]; exact hl)
  | _, _, _, _, .tuple items, hag => .tuple (hasTyList_envAgree items hag)
  | _, _, _, _, .array hlen items, hag => .array hlen (hasTyList_envAgree items hag)
  | _, _, _, _, .repeat hx, hag => .repeat (hasTy_envAgree hx hag)
  | _, _, _, _, .index hx, hag => .index (hasTy_envAgree hx hag)
  | _, _, _, _, .project hx hget, hag => .project (hasTy_envAgree hx hag) hget
  | _, _, _, _, .slice hnot hx, hag => .slice hnot (hasTy_envAgree hx hag)
  | _, _, _, _, .construct h1 h2 h3 h4 hctor items, hag =>
    .construct h1 h2 h3 h4 hctor (hasTyList_envAgree items hag)
  | _, _, _, _, .builtin items, hag => .builtin (hasTyList_envAgree items hag)
  | _, _, _, _, .store hx, hag => .store (hasTy_envAgree hx hag)
  | _, _, _, _, .load hx, hag => .load (hasTy_envAgree hx hag)
  | _, _, _, _, .hint hfo hx, hag => .hint hfo (hasTy_envAgree hx hag)
  | _, _, _, _, .neg hx, hag => .neg (hasTy_envAgree hx hag)
  | _, _, _, _, .binary hl hr, hag =>
    .binary
      (hasTy_envAgree hl fun x hx => hag x (by simp [hasFreeVar, hx]))
      (hasTy_envAgree hr fun x hx => hag x (by simp [hasFreeVar, hx]))
  | _, _, _, _, .call hsig items, hag => .call hsig (hasTyList_envAgree items hag)
  | _, _, _, _, .letValue hx hp hb, hag =>
    .letValue
      (hasTy_envAgree hx fun x hfx => hag x (by simp [hasFreeVar, hfx]))
      hp
      (hasTy_envAgree hb fun x hfb => lookup_append_agree fun hnot => by
        rw [hp.dom_eq] at hnot
        exact hag x (by simp [hasFreeVar, hnot, hfb]))
  | _, _, _, _, .matchValue hs harms, hag =>
    .matchValue
      (hasTy_envAgree hs fun x hfs => hag x (by simp [hasFreeVar, hfs]))
      (hasTyArms_envAgree harms fun x hfa => hag x (by simp [hasFreeVar, hfa]))

theorem hasTyList_envAgree {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ1 Γ2 : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList sigs enums Γ1 xs ts →
      (∀ x, hasFreeVarList x xs = true → Γ1.lookup x = Γ2.lookup x) →
      HasTyList sigs enums Γ2 xs ts
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons hd tl, hag =>
    .cons
      (hasTy_envAgree hd fun x hx => hag x (by simp [hasFreeVarList, hx]))
      (hasTyList_envAgree tl fun x hx => hag x (by simp [hasFreeVarList, hx]))

theorem hasTyArms_envAgree {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ1 Γ2 : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms sigs enums Γ1 ts arms tb →
      (∀ x, hasFreeVarArms x arms = true → Γ1.lookup x = Γ2.lookup x) →
      HasTyArms sigs enums Γ2 ts arms tb
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons hp hb tl, hag =>
    .cons hp
      (hasTy_envAgree hb fun x hx => lookup_append_agree fun hnot => by
        rw [hp.dom_eq] at hnot
        exact hag x (by simp [hasFreeVarArms, hnot, hx]))
      (hasTyArms_envAgree tl fun x hx => hag x (by simp [hasFreeVarArms, hx]))

end

/-- Every function in `fns` is well-typed with respect to `sigs` and `enums`. -/
def ProgWellTyped (sigs : FnSigs) (enums : List Aiur.Generic.EnumDecl) (fns : List Fn) : Prop :=
  ∀ f ∈ fns, HasTy sigs enums f.params f.body f.result

/-! ### Typing Soundness & Typed World-Transfer (`evalExprN_transfer_typed`, `evalExpr_valOk`) -/

section EvalValOk

variable {F : Type} [Field F] [DecidableEq F]

private theorem forall₂_append {α β : Type} {R : α → β → Prop} {l1 l3 : List α} {l2 l4 : List β}
    (h1 : List.Forall₂ R l1 l2) (h2 : List.Forall₂ R l3 l4) :
    List.Forall₂ R (l1 ++ l3) (l2 ++ l4) := by
  induction h1 with
  | nil => exact h2
  | cons hd _ ih => exact .cons hd ih

mutual

/-- Matching a typed pattern `p` against a valid value `v` yields valid bindings for `Δ`. -/
theorem patHasTy_matchPattern {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {h : Heap F} {b : Nat} :
    ∀ {p : Pat} {t : Lower.Ty} {Δ : TyEnv} {v : SourceValue F} {bs : Environment F Nat},
      PatHasTy enums p t Δ →
      ValOk enums h b t v →
      world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) →
      List.Forall₂ (fun x d => x.1 = d.1 ∧ ValOk enums h b d.2 x.2) bs Δ
  | _, _, _, _, _, .wildcard, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; exact .nil
  | .literal n, _, _, v, _, .literal, _, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq] at hm
    cases v with
    | field x =>
      by_cases hx : (n : F) = x
      · subst hx; simp [Aiur.Pattern.bindings] at hm; subst hm; exact .nil
      · simp [Aiur.Pattern.bindings, hx] at hm
    | _ => simp [Aiur.Pattern.bindings] at hm
  | _, _, _, _, _, .bind, hv, hm => by
    simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
    subst hm; exact .cons ⟨rfl, hv⟩ .nil
  | _, _, _, v, _, .tuple (ps := ps) (ts := ts) items, hv, hm => by
    cases v with
    | tuple vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases hlen : (ps.length != vals.length) = true
      · simp [hlen, pure, Except.pure] at hm
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        have hlenEq : ps.length = vals.length := by
          simpa [bne_iff_ne] using hlen
        have hpts : ps.length = ts.length := patListHasTy_length items
        have htsLen : ts.length = vals.length := hpts.symm.trans hlenEq
        unfold ValOk at hv
        have hvalAll : List.Forall₂ (ValOk enums h b) ts vals :=
          List.forall₂_iff_get.mpr ⟨htsLen, fun i hi1 hi2 =>
            hv (ts[i], vals[i]) (mem_zip_of_getElem? (List.getElem?_eq_getElem hi1) (List.getElem?_eq_getElem hi2))⟩
        exact patListHasTy_matchList items hvalAll hm
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
  | _, _, _, v, _, .array (ps := ps) (t := t) (n := n) items, hv, hm => by
    cases v with
    | tuple vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases hlen : (ps.length != vals.length) = true
      · simp [hlen, pure, Except.pure] at hm
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        have hlenEq : ps.length = vals.length := by simpa [bne_iff_ne] using hlen
        have helems := ValOk_array_elem hv
        have hvalAll : List.Forall₂ (ValOk enums h b) (List.replicate ps.length t) vals :=
          List.forall₂_iff_get.mpr ⟨by simp [hlenEq], fun i hi1 hi2 => by
            simp only [List.get_eq_getElem, List.getElem_replicate]
            exact helems vals[i] (List.getElem_mem hi2)⟩
        exact patListHasTy_matchList items hvalAll hm
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm
  | _, _, _, v, _, .construct (en := en) (ctor := ctor) (ps := ps) (fts := fts) hne4 hctor items, hv, hm => by
    cases v with
    | construct qen c vals =>
      simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, List.length_map] at hm
      by_cases htest : (qen != constructorName [] (qualifyTy (.named en [])) ||
          c != ctor || (ps.length != vals.length)) = true
      · simp [htest, pure, Except.pure] at hm
      · simp only [htest, Bool.false_eq_true, ↓reduceIte] at hm
        rw [matchListWith_attach, matchListWith_map, matchListWith_map] at hm
        simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_ne_iff] at htest
        obtain ⟨⟨hqen, rfl⟩, hlenEq⟩ := htest
        have hcn : constructorName [] (qualifyTy (.named en [])) = qualifyName en := by
          simp [constructorName, qualifyTy, Aiur.Generic.Ty.toCore, Instance.symbol]
        rw [hcn] at hqen
        have hpts : ps.length = fts.length := patListHasTy_length items
        have hftsLen : fts.length = vals.length := hpts.symm.trans hlenEq
        unfold ValOk at hv
        by_cases he1 : en = "UInt32::U32"
        · subst he1; simp at hv; obtain ⟨_, _, _, _, _, _, _, _, _, _, hbad⟩ := hv; cases hbad
        · by_cases he2 : en = "UInt32::Compact"
          · subst he2; simp at hv
          · by_cases he3 : en = "UInt8::U8"
            · subst he3; simp at hv
            · simp only [beq_false_of_ne he1, beq_false_of_ne he2, beq_false_of_ne he3,
                beq_false_of_ne hne4, Bool.false_eq_true, ↓reduceIte] at hv
              have hv' := hv hqen
              rw [hctor] at hv'
              have hvalAll : List.Forall₂ (ValOk enums h b) fts vals :=
                List.forall₂_iff_get.mpr ⟨hftsLen, fun i hi1 hi2 =>
                  hv' (fts[i], vals[i]) (mem_zip_of_getElem? (List.getElem?_eq_getElem hi1) (List.getElem?_eq_getElem hi2))⟩
              exact patListHasTy_matchList items hvalAll hm
    | field _ | ptr _ _ | tuple _ =>
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure] at hm

theorem patListHasTy_matchList {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {h : Heap F} {b : Nat} :
    ∀ {ps : List Pat} {ts : List Lower.Ty} {Δ : TyEnv} {vs : List (SourceValue F)} {bs : Environment F Nat},
      PatListHasTy enums ps ts Δ →
      List.Forall₂ (ValOk enums h b) ts vs →
      matchListWith (fun q val => world.matchPattern [] h (qualifyPatF F q) val) ps vs = .ok (some bs) →
      List.Forall₂ (fun x d => x.1 = d.1 ∧ ValOk enums h b d.2 x.2) bs Δ
  | _, _, _, _, _, .nil, .nil, hml => by
    simp only [matchListWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hml
    subst hml; exact .nil
  | p :: ps, _ :: _, _, v :: vs, _, .cons hd tl, .cons hv hvs, hml => by
    simp only [matchListWith, bind, Except.bind] at hml
    cases h1 : world.matchPattern [] h (qualifyPatF F p) v with
    | error _ => rw [h1] at hml; cases hml
    | ok o1 =>
      cases o1 with
      | none => rw [h1] at hml; cases hml
      | some b1 =>
        rw [h1] at hml
        cases h2 : matchListWith (fun q val => world.matchPattern [] h (qualifyPatF F q) val) ps vs with
        | error _ => rw [h2] at hml; cases hml
        | ok o2 =>
          cases o2 with
          | none => rw [h2] at hml; cases hml
          | some b2 =>
            rw [h2] at hml
            simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hml
            subst hml
            exact forall₂_append (patHasTy_matchPattern hd hv h1) (patListHasTy_matchList tl hvs h2)

theorem patListHasTy_length {enums : List Aiur.Generic.EnumDecl} :
    ∀ {ps : List Pat} {ts : List Lower.Ty} {Δ : TyEnv},
      PatListHasTy enums ps ts Δ → ps.length = ts.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ tl => congrArg Nat.succ (patListHasTy_length tl)

end

/-- Library function calls preserve `ValOk` under `U32WorldSpec`. -/
theorem libFnSig_valOk {world : World F} {enums : List Aiur.Generic.EnumDecl}
    (spec : U32WorldSpec world) {qnm : String} {ptys : List Lower.Ty} {rty : Lower.Ty}
    (hsig : libFnSig qnm = some (ptys, rty))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hargs : List.Forall₂ (ValOk enums h h.length) ptys args)
    (ev : EvalFn world qnm args h r h') :
    ValOk enums h' h'.length rty r := by
  unfold libFnSig at hsig
  split at hsig
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.peep.add a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.sub a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.peep.xor a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.and a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.peep.or a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.peep.xor_rotr7 a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨hr, _⟩ := spec.peep.xor_rotr12 a b _ _ _ _ _ ha' hb' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _ | _⟩⟩⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨b, hb'⟩ := (ValOk_u32 ..).mp hb
    obtain ⟨c, hc'⟩ := (ValOk_u32 ..).mp hc
    obtain ⟨hr, _⟩ := spec.peep.add3 a b c _ _ _ _ _ _ ha' hb' hc' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | _⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨hr, _⟩ := spec.peep.rotr8 a _ _ _ _ ha' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | _⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨hr, _⟩ := spec.peep.rotr16 a _ _ _ _ ha' ev
    exact (ValOk_u32 ..).mpr ⟨_, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | _⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨rfl, _⟩ := spec.peep.to_bytes a _ _ _ _ ha' ev
    exact (ValOk_u8Array4 ..).mpr ⟨a, ha'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | _⟩
    obtain ⟨a, ha'⟩ := (ValOk_u8Array4 ..).mp ha
    obtain ⟨rfl, _⟩ := spec.peep.from_bytes a _ _ _ _ ha' ev
    exact (ValOk_u32 ..).mpr ⟨a, ha'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | _⟩
    obtain ⟨a, ha'⟩ := (ValOk_u32 ..).mp ha
    obtain ⟨rfl, _⟩ := spec.tg.compact a _ _ _ _ ha' ev
    exact (ValOk_compact ..).mpr ⟨a, isU32Val_lt ha', rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨_, _ | _⟩
    obtain ⟨hr, _⟩ := spec.from_fields_any _ _ _ _ ev
    exact (ValOk_u32 ..).mpr hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨_, _ | _⟩
    obtain ⟨n, _, _, hr, _⟩ := spec.tg.from_field _ _ _ _ ev
    exact (ValOk_u32 ..).mpr ⟨n, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, haLt, rfl⟩ := (ValOk_compact ..).mp ha
    obtain ⟨b, hbLt, rfl⟩ := (ValOk_compact ..).mp hb
    obtain ⟨⟨w, vf, rfl, n, hn⟩, _⟩ := spec.u32_sub_borrow a b h r h' haLt hbLt ev
    unfold ValOk
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (ValOk_u32 ..).mpr ⟨n, hn⟩
    · simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨_, _ | _⟩
    obtain ⟨hr, _⟩ := spec.u32_compact_from_field _ _ _ _ ev
    exact (ValOk_compact ..).mpr hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | _⟩
    obtain ⟨a, haLt, rfl⟩ := (ValOk_compact ..).mp ha
    obtain ⟨hr, _⟩ := spec.u32_expand a h r h' haLt ev
    exact (ValOk_u32 ..).mpr ⟨a, hr⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
    obtain ⟨_, a, b, haLt, hbLt, rfl, rfl, rfl⟩ := spec.peep.u8_from_fields _ _ _ _ _ ev
    unfold ValOk
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (ValOk_u8 ..).mpr ⟨a, haLt, rfl⟩
    · exact (ValOk_u8 ..).mpr ⟨b, hbLt, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, haLt, rfl⟩ := (ValOk_u8 ..).mp ha
    obtain ⟨b, hbLt, rfl⟩ := (ValOk_u8 ..).mp hb
    obtain ⟨hr, _⟩ := spec.u8_xor a b h r h' haLt hbLt ev
    exact (ValOk_u8 ..).mpr hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, haLt, rfl⟩ := (ValOk_u8 ..).mp ha
    obtain ⟨b, hbLt, rfl⟩ := (ValOk_u8 ..).mp hb
    obtain ⟨hr, _⟩ := spec.u8_and a b h r h' haLt hbLt ev
    exact (ValOk_u8 ..).mpr hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
    obtain ⟨a, haLt, rfl⟩ := (ValOk_u8 ..).mp ha
    obtain ⟨b, hbLt, rfl⟩ := (ValOk_u8 ..).mp hb
    obtain ⟨hr, _⟩ := spec.u8_or a b h r h' haLt hbLt ev
    exact (ValOk_u8 ..).mpr hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    unfold ValOk; cases r <;> simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    unfold ValOk; cases r <;> try trivial
    intro p hp
    have hm := (List.of_mem_zip hp).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h1 | h1 <;> rw [h1] <;> simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    unfold ValOk; cases r <;> try trivial
    intro p hp
    have hm := (List.of_mem_zip hp).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h1 | h1 <;> rw [h1] <;> simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
    simp
  · cases hsig

section TransferTyped

set_option linter.unusedSectionVars false

private theorem transfer_matchPattern {w1 w2 : World F} (haux : SameAuxWorld w1 w2)
    {h : Heap F} {p : Pat} {v : SourceValue F} {bs : Environment F Nat}
    (hm : w1.matchPattern [] h (qualifyPatF F p) v = .ok (some bs)) :
    w2.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) := by
  rw [← haux.matchPattern_eq]; exact hm

private theorem transfer_selectArm {w1 w2 : World F} (haux : SameAuxWorld w1 w2)
    {h : Heap F} {v : SourceValue F} {arms : List (Aiur.Generic.Pattern F × Aiur.Generic.Expr F)}
    {res : Environment F Nat × Aiur.Generic.Expr F}
    (hsel : SourceSemantics.selectArm w1 [] h v arms = .ok (some res)) :
    SourceSemantics.selectArm w2 [] h v arms = .ok (some res) := by
  rw [← haux.selectArm_eq]; exact hsel

private theorem transfer_typed {w1 w2 : World F} (haux : SameAuxWorld w1 w2)
    {t : Aiur.Ty} {v : Constant F} (ht : w1.typed t v = true) :
    w2.typed t v = true := by
  rw [← haux.typed_eq]; exact ht

variable {w1 w2 : World F} {d : Nat} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl}
  (haux : SameAuxWorld w1 w2)
  (hcall : ∀ d' < d, ∀ qnm ptys rty args h r h',
    sigs qnm = some (ptys, rty) →
    List.Forall₂ (ValOk enums h h.length) ptys args →
    EvalFnN w1 d' qnm args h r h' →
    EvalFn w2 qnm args h r h' ∧ ValOk enums h' h'.length rty r)

include haux hcall in
mutual

/-- Simultaneous depth-indexed world transfer AND `ValOk` preservation for well-typed expressions. -/
theorem evalExprN_transfer_typed :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {e : Expr} {t : Lower.Ty}
      {h h' : Heap F} {r : SourceValue F},
      HasTy sigs enums Γ e t →
      EnvOk enums h h.length Γ locals →
      EvalExprN w1 d [] locals (qualifyExprF F e) h r h' →
      EvalExpr w2 [] locals (qualifyExprF F e) h r h' ∧ ValOk enums h' h'.length t r
  | _, _, _, _, _, _, _, .literal, _, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev
    exact ⟨.literal, by simp⟩
  | _, _, _, _, _, _, _, .var hl, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | var hfound =>
      obtain ⟨v, hv, hok⟩ := henv _ _ hl
      rw [hfound, Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨_, rfl⟩ := hv
      exact ⟨.var hfound, hok⟩
  | _, _, _, _, _, _, _, .tuple items, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with
    | tuple xs =>
      obtain ⟨xs2, hvals⟩ := evalArgsN_transfer_typed items henv xs
      refine ⟨.tuple xs2, ?_⟩
      unfold ValOk
      intro p hp
      obtain ⟨i, hi1, hpi⟩ := List.mem_iff_getElem.mp hp
      rw [List.getElem_zip] at hpi
      rw [← hpi]
      have hget := (List.forall₂_iff_get.mp hvals).2 i (by simp at hi1; omega) (by simp at hi1; omega)
      simpa [List.get_eq_getElem] using hget
  | _, _, _, _, _, _, _, .array (t := t) (n := n) hlen items, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with
    | array xs =>
      obtain ⟨xs2, hvals⟩ := evalArgsN_transfer_typed items henv xs
      refine ⟨.array xs2, ValOk_array_of_elems ?_ ?_⟩
      · have := hvals.length_eq
        simp at this
        exact this.symm
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hlenEq := hvals.length_eq
        have hi' : i < (List.replicate n t).length := by omega
        have hget := (List.forall₂_iff_get.mp hvals).2 i hi' hi
        simpa [List.get_eq_getElem, List.getElem_replicate] using hget
  | _, _, _, _, _, _, _, .repeat hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | «repeat» item =>
      obtain ⟨item2, hok⟩ := evalExprN_transfer_typed hx henv item
      refine ⟨.repeat item2, ValOk_array_of_elems (List.length_replicate) ?_⟩
      intro x hxMem
      rw [List.eq_of_mem_replicate hxMem]
      exact hok
  | _, _, _, _, _, _, _, .index (i := idx) hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | index item hproj =>
      obtain ⟨item2, hok⟩ := evalExprN_transfer_typed hx henv item
      refine ⟨.index item2 hproj, ?_⟩
      rename_i val
      cases val with
      | tuple vs =>
        simp only [projectValue] at hproj
        cases hget : vs[idx]? with
        | none => rw [hget] at hproj; cases hproj
        | some res =>
          rw [hget] at hproj
          simp only [pure, Except.pure, Except.ok.injEq] at hproj
          subst hproj
          exact ValOk_array_elem hok _ (List.mem_of_getElem? hget)
      | field _ | ptr _ _ | construct _ _ _ => simp [projectValue] at hproj
  | _, _, _, _, _, _, _, .project (i := idx) hx hget, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | project item hproj =>
      obtain ⟨item2, hok⟩ := evalExprN_transfer_typed hx henv item
      refine ⟨.project item2 hproj, ?_⟩
      rename_i val
      cases val with
      | tuple vs =>
        simp only [projectValue] at hproj
        cases hgv : vs[idx]? with
        | none => rw [hgv] at hproj; cases hproj
        | some res =>
          rw [hgv] at hproj
          simp only [pure, Except.pure, Except.ok.injEq] at hproj
          subst hproj
          unfold ValOk at hok
          exact hok (_, _) (mem_zip_of_getElem? hget hgv)
      | field _ | ptr _ _ | construct _ _ _ => simp [projectValue] at hproj
  | _, _, _, _, _, _, _, .slice (t := t) (m := m) hnot hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | slice item hsliced =>
      obtain ⟨item2, hok⟩ := evalExprN_transfer_typed hx henv item
      refine ⟨.slice item2 hsliced, ?_⟩
      rename_i val
      cases val with
      | tuple vs =>
        simp only [sliceValue, bind, Except.bind, pure, Except.pure] at hsliced
        split at hsliced
        · cases hsliced
        · simp only [Except.ok.injEq] at hsliced
          subst hsliced
          unfold ValOk
          have hne : (t == u8Ty && m == 4) = false := by
            simp [beq_false_of_ne hnot]
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          intro x hxMem
          exact ValOk_array_elem hok x (List.mem_of_mem_drop (List.mem_of_mem_take hxMem))
      | field _ | ptr _ _ | construct _ _ _ => simp [sliceValue] at hsliced
  | _, _, _, _, _, _, _, .construct h1 h2 h3 h4 hctor items, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with
    | construct xs =>
      obtain ⟨xs2, hvals⟩ := evalArgsN_transfer_typed items henv xs
      refine ⟨.construct xs2, ?_⟩
      unfold ValOk
      simp only [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3,
        beq_false_of_ne h4, Bool.false_eq_true, ↓reduceIte]
      intro _
      rw [hctor]
      intro p hp
      obtain ⟨i, hi1, hpi⟩ := List.mem_iff_getElem.mp hp
      rw [List.getElem_zip] at hpi
      rw [← hpi]
      have hget := (List.forall₂_iff_get.mp hvals).2 i (by simp at hi1; omega) (by simp at hi1; omega)
      simpa [List.get_eq_getElem] using hget
  | _, _, _, _, _, _, r, .builtin items, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with
    | builtin xs ha =>
      obtain ⟨xs2, _⟩ := evalArgsN_transfer_typed items henv xs
      refine ⟨.builtin xs2 ha, ?_⟩
      unfold ValOk; cases r <;> simp
  | _, _, _, _, _, _, _, .store hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | store item =>
      obtain ⟨item2, hok⟩ := evalExprN_transfer_typed hx henv item
      refine ⟨.store item2, ?_⟩
      unfold ValOk
      refine ⟨by simp, _, by simp, hok.mono (Heap.Extends.snoc _ _) (Nat.le_refl _)⟩
  | _, _, _, _, _, _, _, .load hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | load item hload =>
      obtain ⟨item2, hok⟩ := evalExprN_transfer_typed hx henv item
      refine ⟨.load item2 hload, ?_⟩
      rename_i val
      cases val with
      | ptr pt addr =>
        unfold ValOk at hok
        obtain ⟨hlt, w, hget, hw⟩ := hok
        simp only [loadValue, hget, pure, Except.pure] at hload
        split at hload
        · cases hload
        · simp only [bind, Except.bind, Except.ok.injEq] at hload
          subst hload
          exact hw.mono (Heap.Extends.refl _) (Nat.le_of_lt hlt)
      | field _ | tuple _ | construct _ _ _ => simp [loadValue] at hload
  | _, _, _, _, _, _, _, .hint hfo hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | hint item ht =>
      obtain ⟨item2, _⟩ := evalExprN_transfer_typed hx henv item
      exact ⟨.hint item2 (transfer_typed haux ht), ValOk_of_isFieldOnlyTy _ hfo⟩
  | _, _, _, _, _, _, _, .neg hx, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | neg item hop =>
      obtain ⟨item2, _⟩ := evalExprN_transfer_typed hx henv item
      exact ⟨.neg item2 hop, by simp⟩
  | _, _, _, _, _, _, _, .binary hl hr, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary el er hop =>
      obtain ⟨el2, _⟩ := evalExprN_transfer_typed hl henv el
      have hext := el2.heap_extends
      obtain ⟨er2, _⟩ := evalExprN_transfer_typed hr (henv.mono hext hext.length_le) er
      exact ⟨.binary el2 er2 hop, by simp⟩
  | _, _, _, _, _, _, _, .call (nm := nm) hsig items, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with
    | call hlt xs cal =>
      obtain ⟨xs2, hvals⟩ := evalArgsN_transfer_typed items henv xs
      have hinst : instanceName [] (qualifyName nm) (Option.map (List.map qualifyTy) (some [])) =
          qualifyName nm := by
        simp [instanceName, Instance.symbol]
      rw [hinst] at cal
      obtain ⟨cal2, hok⟩ := hcall _ hlt _ _ _ _ _ _ _ hsig hvals cal
      exact ⟨.call xs2 (by rw [hinst]; exact cal2), hok⟩
  | _, _, _, _, _, _, _, .letValue hx hp hb, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | letValue evX hm evB =>
      obtain ⟨evX2, hokX⟩ := evalExprN_transfer_typed hx henv evX
      have hext := evX2.heap_extends
      have hm2 := transfer_matchPattern haux hm
      have hbs := patHasTy_matchPattern hp hokX hm2
      have henvB := envOk_append hbs (henv.mono hext hext.length_le)
      obtain ⟨evB2, hokB⟩ := evalExprN_transfer_typed hb henvB evB
      exact ⟨.letValue evX2 hm2 evB2, hokB⟩
  | _, _, _, _, _, _, _, .matchValue hs harms, henv, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | matchValue evS hsel evB =>
      obtain ⟨evS2, hokS⟩ := evalExprN_transfer_typed hs henv evS
      have hext := evS2.heap_extends
      have hsel2 := transfer_selectArm haux hsel
      have hsel2' := hsel2
      rw [map_qualifyArmsF] at hsel2'
      obtain ⟨p, b, hmem, rfl, hm⟩ := selectArm_map_inv hsel2'
      obtain ⟨Δ, hp, hb⟩ := harms.mem hmem
      have hbs := patHasTy_matchPattern hp hokS hm
      have henvB := envOk_append hbs (henv.mono hext hext.length_le)
      obtain ⟨evB2, hokB⟩ := evalExprN_transfer_typed hb henvB evB
      exact ⟨.matchValue evS2 hsel2 evB2, hokB⟩
termination_by _ _ e _ _ _ _ _ _ _ => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgsN_transfer_typed :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {xs : List Expr} {ts : List Lower.Ty}
      {h h' : Heap F} {vs : List (SourceValue F)},
      HasTyList sigs enums Γ xs ts →
      EnvOk enums h h.length Γ locals →
      EvalArgsN w1 d [] locals (xs.map (qualifyExprF F)) h vs h' →
      EvalArgs w2 [] locals (xs.map (qualifyExprF F)) h vs h' ∧
        List.Forall₂ (ValOk enums h' h'.length) ts vs
  | _, _, _, _, _, _, _, .nil, _, ev => by
    cases ev; exact ⟨.nil, .nil⟩
  | _, _, _, _, _, _, _, .cons hd tl, henv, ev => by
    cases ev with
    | cons evH evT =>
      obtain ⟨evH2, hokH⟩ := evalExprN_transfer_typed hd henv evH
      have hext1 := evH2.heap_extends
      obtain ⟨evT2, hokT⟩ := evalArgsN_transfer_typed tl (henv.mono hext1 hext1.length_le) evT
      have hext2 := evT2.heap_extends
      exact ⟨.cons evH2 evT2, .cons (hokH.mono hext2 hext2.length_le) hokT⟩
termination_by _ _ xs _ _ _ _ _ _ _ => sizeOf xs

end

end TransferTyped

/-- **Generic Typed Program-Body Transformation Lifting Lemma:**
Lifts any per-function same-world body backward simulation (which may assume `EnvOk`
for all parameters and `HasTy`) to a full world-level `EvalFn wOpt → EvalFn wOrig ∧ ValOk`! -/
theorem world_transformBodies_typed_backward {wOpt wOrig : World F}
    {enums : List Aiur.Generic.EnumDecl} {fns fns' : List Fn}
    (haux : SameAuxWorld wOpt wOrig)
    (hnd : (fns.map (·.name)).Nodup)
    (hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result)
      fns fns')
    (hOptHas : WorldHasFns wOpt fns')
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : ∀ m a, isProgQName m = false → wOpt.prepare m a = wOrig.prepare m a)
    (hLib : LibSelfContained wOrig)
    (spec : U32WorldSpec wOrig)
    (hWT' : ProgWellTyped (fnSigsOf fns) enums fns')
    (hBodySim : ∀ f f', f ∈ fns → f' ∈ fns' →
      f'.name = f.name → f'.params = f.params → f'.result = f.result →
      ∀ args h r h',
        List.Forall₂ (ValOk enums h h.length) (f.params.map Prod.snd) args →
        EvalExpr wOrig [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f'.body) h r h' →
        EvalExpr wOrig [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f.body) h r h')
    {qnm : String} {ptys : List Lower.Ty} {rty : Lower.Ty}
    (hsig : fnSigsOf fns qnm = some (ptys, rty))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hargs : List.Forall₂ (ValOk enums h h.length) ptys args)
    (ev : EvalFn wOpt qnm args h r h') :
    EvalFn wOrig qnm args h r h' ∧ ValOk enums h' h'.length rty r := by
  have hPair : ∀ f' ∈ fns', ∃ f ∈ fns, f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result := by
    clear hnd hOptHas hOrigProv hNonProg hLib spec hWT' hBodySim hsig hargs ev
    induction hrel with
    | nil => intro _ h; cases h
    | cons h1 _ ih =>
      intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | htl
      · exact ⟨_, List.mem_cons_self, h1.1, h1.2.1, h1.2.2⟩
      · obtain ⟨f, hf, hn, hp, hr⟩ := ih f' htl
        exact ⟨f, List.mem_cons_of_mem _ hf, hn, hp, hr⟩
  have hPairRev : ∀ f ∈ fns, ∃ f' ∈ fns', f'.name = f.name := by
    clear hPair hnd hOptHas hOrigProv hNonProg hLib spec hWT' hBodySim hsig hargs ev
    induction hrel with
    | nil => intro _ h; cases h
    | cons h1 _ ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | htl
      · exact ⟨_, List.mem_cons_self, h1.1⟩
      · obtain ⟨f', hf', hn⟩ := ih f htl
        exact ⟨f', List.mem_cons_of_mem _ hf', hn⟩
  obtain ⟨d, evN⟩ := EvalFnN.ofEvalFn ev
  revert qnm ptys rty hsig args h h' r hargs ev evN
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro qnm ptys rty hsig args h h' r hargs _ evN
    have hcall : ∀ d' < d, ∀ qnm' ptys' rty' args' h1 r1 h2,
        fnSigsOf fns qnm' = some (ptys', rty') →
        List.Forall₂ (ValOk enums h1 h1.length) ptys' args' →
        EvalFnN wOpt d' qnm' args' h1 r1 h2 →
        EvalFn wOrig qnm' args' h1 r1 h2 ∧ ValOk enums h2 h2.length rty' r1 :=
      fun d' hlt qnm' ptys' rty' args' h1 r1 h2 hs' ha' e =>
        ih d' hlt hs' ha' e.toEvalFn e
    by_cases hex : ∃ f' ∈ fns', qualified f'.name = qnm
    · obtain ⟨f', hf', rfl⟩ := hex
      obtain ⟨f, hf, hnm, hpar, hres⟩ := hPair f' hf'
      have hfind : fns.find? (fun g => qualified g.name == qualified f'.name) = some f := by
        rw [hnm]; exact find?_eq_of_nodup hnd hf
      unfold fnSigsOf at hsig
      rw [hfind] at hsig
      simp only [Option.some.injEq, Prod.mk.injEq] at hsig
      obtain ⟨rfl, rfl⟩ := hsig
      cases evN with
      | intro prep body =>
        obtain ⟨rfl, hlen, rfl, rfl⟩ := hOptHas f' hf' args _ _ _ prep
        have henv : EnvOk enums h h.length f'.params ((f'.params.map Prod.fst).zip args) := by
          rw [hpar]; exact envOk_zip hargs
        have ⟨bodyOrig, hok⟩ := evalExprN_transfer_typed haux hcall (hWT' f' hf') henv body
        have bodyOrig' : EvalExpr wOrig [] ((f.params.map Prod.fst).zip args)
            (qualifyExprF F f'.body) h r h' := by
          rw [← hpar]; exact bodyOrig
        have bodySim := hBodySim f f' hf hf' hnm hpar hres args h r h' hargs bodyOrig'
        have prepOrig : wOrig.prepare (qualified f'.name) args =
            .ok ([], (f.params.map Prod.fst).zip args, qualifyExprF F f.body) := by
          rw [hnm]
          exact hOrigProv f hf args (by rw [← hpar]; exact hlen)
        exact ⟨.intro prepOrig bodySim, by rw [← hres]; exact hok⟩
      | returned prep body =>
        obtain ⟨rfl, _, rfl, rfl⟩ := hOptHas f' hf' args _ _ _ prep
        exact False.elim (no_evalExit_of_plain
          (by rw [isPlainExpr_qualifyExprF]; exact (hWT' f' hf').isPlain) body.toEvalExit)
    · have hnotFns : ∀ f ∈ fns, qualified f.name ≠ qnm := by
        intro f hf heq
        obtain ⟨f', hf', hnm⟩ := hPairRev f hf
        exact hex ⟨f', hf', by rw [hnm]; exact heq⟩
      have hfindNone : fns.find? (fun f => qualified f.name == qnm) = none := by
        rw [List.find?_eq_none]
        intro f hf
        simp [beq_false_of_ne (hnotFns f hf)]
      unfold fnSigsOf at hsig
      rw [hfindNone] at hsig
      have hnp := libFnSig_nonProg hsig
      have evOrig : EvalFn wOrig qnm args h r h' :=
        hLib wOpt wOrig qnm args h h' r haux (.refl wOrig) hNonProg (fun _ _ _ => rfl) hnp evN.toEvalFn
      exact ⟨evOrig, libFnSig_valOk spec hsig hargs evOrig⟩

/-- **Single-world `EvalFn` Typing Soundness:**
Every call to a typed function in a well-typed program preserves `ValOk`. -/
theorem evalFn_valOk {world : World F} {enums : List Aiur.Generic.EnumDecl} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns)
    (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world)
    (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns)
    {qnm : String} {ptys : List Lower.Ty} {rty : Lower.Ty}
    (hsig : fnSigsOf fns qnm = some (ptys, rty))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hargs : List.Forall₂ (ValOk enums h h.length) ptys args)
    (ev : EvalFn world qnm args h r h') :
    ValOk enums h' h'.length rty r :=
  (world_transformBodies_typed_backward (.refl world) hnd
    (List.forall₂_iff_get.mpr ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩)
    hHas hProv (fun _ _ _ => rfl) hLib spec hWT
    (fun f f' hf hf' hnm hpar _ args h r h' _ evB => by
      have heq : f' = f := by
        have h1 := find?_eq_of_nodup hnd hf
        have h2 := find?_eq_of_nodup hnd hf'
        rw [hnm] at h2
        rw [h1, Option.some.injEq] at h2
        exact h2.symm
      subst heq; exact evB)
    hsig hargs ev).2

/-- **Single-world `EvalExpr` Typing Soundness:**
Every well-typed expression evaluated in a valid environment returns a `ValOk` value!
In particular, any `u32Ty`-typed expression returns a verified `∃ n, isU32Val n r`. -/
theorem evalExpr_valOk {world : World F} {enums : List Aiur.Generic.EnumDecl} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns)
    (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world)
    (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns)
    {Γ : TyEnv} {locals : Environment F Nat} {e : Expr} {t : Lower.Ty}
    {h h' : Heap F} {r : SourceValue F}
    (hty : HasTy (fnSigsOf fns) enums Γ e t)
    (henv : EnvOk enums h h.length Γ locals)
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ValOk enums h' h'.length t r := by
  obtain ⟨d, evN⟩ := EvalExprN.ofEvalExpr ev
  exact (evalExprN_transfer_typed (SameAuxWorld.refl world)
    (fun _ _ qnm ptys rty args h1 r1 h2 hsig hargs cal =>
      ⟨cal.toEvalFn, evalFn_valOk hnd hHas hProv hLib spec hWT hsig hargs cal.toEvalFn⟩)
    hty henv evN).2

end EvalValOk

end HasTyDef

end TypingAndU32Spec

/-! ## Section 4: `foldConstU32OfField` Backward Soundness -/

section FoldConstU32

/-- Standard signatures of any `Prog` `UInt32` helpers present in `fns`. -/
def HasU32HelperSigs (fns : List Fn) : Prop :=
  (∀ ptys rty, fnSigsOf fns (qualified "u32_of_field") = some (ptys, rty) →
    ptys = [.field] ∧ rty = u32Ty) ∧
  (∀ ptys rty, fnSigsOf fns (qualified "u32_shr") = some (ptys, rty) →
    ptys = [u32Ty, u32Ty] ∧ rty = u32Ty) ∧
  (∀ ptys rty, fnSigsOf fns (qualified "u32_shl") = some (ptys, rty) →
    ptys = [u32Ty, u32Ty] ∧ rty = u32Ty) ∧
  (∀ ptys rty, fnSigsOf fns (qualified "u32_mul") = some (ptys, rty) →
    ptys = [u32Ty, u32Ty] ∧ rty = u32Ty)

theorem fnSigsOf_nonProg (fns : List Fn) {qnm : String} (hnp : isProgQName qnm = false) :
    fnSigsOf fns qnm = libFnSig qnm := by
  unfold fnSigsOf
  have hnone : fns.find? (fun f => qualified f.name == qnm) = none := by
    rw [List.find?_eq_none]
    intro f _
    simp only [beq_iff_eq]
    intro heq
    subst heq
    rw [isProgQName_qualified] at hnp
    cases hnp
  rw [hnone]

mutual

/-- `foldConstU32OfField` preserves `HasTy`. -/
theorem hasTy_foldConstU32OfField {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy (fnSigsOf fns) enums Γ e t →
      HasTy (fnSigsOf fns) enums Γ (foldConstU32OfField e) t
  | _, _, _, .literal => .literal
  | _, _, _, .var hl => .var hl
  | _, _, _, .tuple items => .tuple (hasTy_foldConstU32OfFieldList hSigs items)
  | _, _, _, .array hlen items =>
    .array (by rw [foldConstU32OfFieldList_length]; exact hlen)
      (hasTy_foldConstU32OfFieldList hSigs items)
  | _, _, _, .repeat hx => .repeat (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .index hx => .index (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .project hx hget => .project (hasTy_foldConstU32OfField hSigs hx) hget
  | _, _, _, .slice hnot hx => .slice hnot (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .construct h1 h2 h3 h4 hctor items =>
    .construct h1 h2 h3 h4 hctor (hasTy_foldConstU32OfFieldList hSigs items)
  | _, _, _, .builtin items => .builtin (hasTy_foldConstU32OfFieldList hSigs items)
  | _, _, _, .store hx => .store (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .load hx => .load (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .hint hfo hx => .hint hfo (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .neg hx => .neg (hasTy_foldConstU32OfField hSigs hx)
  | _, _, _, .binary hl hr =>
    .binary (hasTy_foldConstU32OfField hSigs hl) (hasTy_foldConstU32OfField hSigs hr)
  | _, _, _, .call (nm := nm) (xs := xs) hsig items => by
    unfold foldConstU32OfField
    split
    · next n =>
      split
      · have hq : qualifyName "u32_of_field" = qualified "u32_of_field" := rfl
        rw [hq] at hsig
        obtain ⟨_, rfl⟩ := hSigs.1 _ _ hsig
        refine .call (ptys := [.array .field 4]) ?_ ?_
        · rw [TypedGadgets.qualifyName_u32_from_fields, fnSigsOf_nonProg fns rfl]; rfl
        · exact .cons (.array rfl (.cons .literal (.cons .literal (.cons .literal (.cons .literal .nil))))) .nil
      · exact .call hsig (hasTy_foldConstU32OfFieldList hSigs items)
    · exact .call hsig (hasTy_foldConstU32OfFieldList hSigs items)
  | _, _, _, .letValue hx hp hb =>
    .letValue (hasTy_foldConstU32OfField hSigs hx) hp (hasTy_foldConstU32OfField hSigs hb)
  | _, _, _, .matchValue hs harms =>
    .matchValue (hasTy_foldConstU32OfField hSigs hs) (hasTy_foldConstU32OfFieldArms hSigs harms)

theorem hasTy_foldConstU32OfFieldList {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList (fnSigsOf fns) enums Γ xs ts →
      HasTyList (fnSigsOf fns) enums Γ (foldConstU32OfFieldList xs) ts
  | _, _, _, .nil => .nil
  | _, _, _, .cons hd tl =>
    .cons (hasTy_foldConstU32OfField hSigs hd) (hasTy_foldConstU32OfFieldList hSigs tl)

theorem hasTy_foldConstU32OfFieldArms {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms (fnSigsOf fns) enums Γ ts arms tb →
      HasTyArms (fnSigsOf fns) enums Γ ts (foldConstU32OfFieldArms arms) tb
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hp hb tl =>
    .cons hp (hasTy_foldConstU32OfField hSigs hb) (hasTy_foldConstU32OfFieldArms hSigs tl)

theorem foldConstU32OfFieldList_length :
    ∀ (xs : List Expr), (foldConstU32OfFieldList xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (foldConstU32OfFieldList_length xs)

end

section FoldConstEval

variable {F : Type} [Field F] [DecidableEq F]

/-- Generic `selectArm` transfer when a transformation only rewrites arm bodies (keeping
patterns identical). Reused across `foldConstU32OfField`, `Peephole`, `flattenLets`,
`inlineCallsM`, and `simpExpr`! -/
theorem selectArm_mapBody {world : World F} {h : Heap F} {v : SourceValue F}
    (f : Pat → Expr → Expr) :
    ∀ {arms : List (Pat × Expr)} {bs : Environment F Nat} {bodyF : Aiur.Generic.Expr F},
      SourceSemantics.selectArm world [] h v
        (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F (f arm.1 arm.2))) =
        .ok (some (bs, bodyF)) →
      ∃ p b, (p, b) ∈ arms ∧ bodyF = qualifyExprF F (f p b) ∧
        world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) ∧
        SourceSemantics.selectArm world [] h v
          (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
          .ok (some (bs, qualifyExprF F b))
  | [], _, _, hsel => by simp [SourceSemantics.selectArm, pure, Except.pure] at hsel
  | (p, b) :: rest, bs, bodyF, hsel => by
    simp only [List.map_cons, SourceSemantics.selectArm, bind, Except.bind] at hsel ⊢
    cases hm : world.matchPattern [] h (qualifyPatF F p) v with
    | error _ => rw [hm] at hsel; cases hsel
    | ok o =>
      cases o with
      | some bs' =>
        rw [hm] at hsel
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨p, b, List.mem_cons_self, rfl, hm, rfl⟩
      | none =>
        rw [hm] at hsel
        obtain ⟨p', b', hmem, heq, hm', hsel'⟩ := selectArm_mapBody f hsel
        exact ⟨p', b', List.mem_cons_of_mem _ hmem, heq, hm', hsel'⟩

private theorem foldConstU32OfFieldArms_eq_map (arms : List (Pat × Expr)) :
    foldConstU32OfFieldArms arms = arms.map fun arm => (arm.1, foldConstU32OfField arm.2) := by
  induction arms with
  | nil => rfl
  | cons a tl ih => rcases a with ⟨p, b⟩; simp [foldConstU32OfFieldArms, ih]

private theorem foldConstU32OfFieldList_eq_map (xs : List Expr) :
    foldConstU32OfFieldList xs = xs.map foldConstU32OfField := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [foldConstU32OfFieldList, ih]

mutual

/-- **Stage 2 (`foldConstU32OfField`) Same-World Backward Soundness:**
Any `EvalExpr` derivation on `foldConstU32OfField e` lifts to `EvalExpr` on `e`
with identical locals, heap, and return value! -/
theorem evalExpr_foldConstU32OfField_backward {world : World F} (spec : U32WorldSpec world) :
    ∀ {e : Expr} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      EvalExpr world [] locals (qualifyExprF F (foldConstU32OfField e)) h r h' →
      EvalExpr world [] locals (qualifyExprF F e) h r h'
  | .literal _, _, _, _, _, ev | .var _, _, _, _, _, ev
  | .global _ _, _, _, _, _, ev | .control _ _, _, _, _, _, ev => ev
  | .tuple xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple items => exact .tuple (evalArgs_foldConstU32OfField_backward spec items)
  | .array xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array items => exact .array (evalArgs_foldConstU32OfField_backward spec items)
  | .construct ty targs nm xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct items => exact .construct (evalArgs_foldConstU32OfField_backward spec items)
  | .constructAs ps ty nm xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | constructAs items => exact .constructAs (evalArgs_foldConstU32OfField_backward spec items)
  | .record hd xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | record items => exact .record (evalArgs_foldConstU32OfField_backward spec items)
  | .update ps xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | update items ha => exact .update (evalArgs_foldConstU32OfField_backward spec items) ha
  | .builtin op xs, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin items ha => exact .builtin (evalArgs_foldConstU32OfField_backward spec items) ha
  | .repeat x n, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item => exact .repeat (evalExpr_foldConstU32OfField_backward spec item)
  | .index x i, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp => exact .index (evalExpr_foldConstU32OfField_backward spec item) hp
  | .slice x a b, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs => exact .slice (evalExpr_foldConstU32OfField_backward spec item) hs
  | .member x f, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | member item hp => exact .member (evalExpr_foldConstU32OfField_backward spec item) hp
  | .project x i, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp => exact .project (evalExpr_foldConstU32OfField_backward spec item) hp
  | .store x, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item => exact .store (evalExpr_foldConstU32OfField_backward spec item)
  | .load x, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl => exact .load (evalExpr_foldConstU32OfField_backward spec item) hl
  | .hint ty x ch, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht => exact .hint (evalExpr_foldConstU32OfField_backward spec item) ht
  | .neg x, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop => exact .neg (evalExpr_foldConstU32OfField_backward spec item) hop
  | .binary op l r, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary el er hop =>
      exact .binary
        (evalExpr_foldConstU32OfField_backward spec el)
        (evalExpr_foldConstU32OfField_backward spec er) hop
  | .letValue p x b, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | letValue evX hm evB =>
      exact .letValue
        (evalExpr_foldConstU32OfField_backward spec evX) hm
        (evalExpr_foldConstU32OfField_backward spec evB)
  | .matchValue s arms, _, _, _, _, ev => by
    simp only [foldConstU32OfField, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | matchValue evS hsel evB =>
      rw [map_qualifyArmsF, foldConstU32OfFieldArms_eq_map, List.map_map] at hsel
      have hsel' : SourceSemantics.selectArm world [] _ _
          (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F (foldConstU32OfField arm.2))) =
          .ok (some (_, _)) := hsel
      obtain ⟨p, b, hmem, rfl, _, hselOrig⟩ :=
        selectArm_mapBody (fun _ b => foldConstU32OfField b) hsel'
      rw [← map_qualifyArmsF] at hselOrig
      exact .matchValue
        (evalExpr_foldConstU32OfField_backward spec evS)
        hselOrig
        (evalExpr_foldConstU32OfField_backward spec evB)
  | .call nm targs xs, _, _, _, _, ev => by
    unfold foldConstU32OfField at ev
    split at ev
    · next n =>
      split at ev
      · next hn =>
        simp only [qualifyExprF, qualifyExpr, TypedGadgets.qualifyName_u32_from_fields,
          TypedGadgets.qualifyName_u32_of_field, Option.map_some, List.map,
          Aiur.Generic.Expr.map] at ev ⊢
        obtain ⟨varr, hm, evArr, hfn⟩ := evalExpr_call1_inv ev
        obtain ⟨v0, v1, v2, v3, h1, h2, h3, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evArr
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e2
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e3
        obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, he0, he1, he2, he3, hrU32, rfl⟩ :=
          spec.tg.from_fields _ _ _ _ _ _ _ hfn
        set m := n % 4294967296
        have hmEq : m = n % U32.base := rfl
        have hlt : m < 4294967296 := Nat.mod_lt n (by omega)
        have hb0 : m % 256 < 256 := Nat.mod_lt _ (by omega)
        have hb1 : (m / 256) % 256 < 256 := Nat.mod_lt _ (by omega)
        have hb2 : (m / 65536) % 256 < 256 := Nat.mod_lt _ (by omega)
        have hb3 : (m / 16777216) % 256 < 256 := Nat.mod_lt _ (by omega)
        have injByte : ∀ {a b : Nat}, a < 256 → b < 256 →
            (Value.field (a : F) : SourceValue F) = .field (b : F) → a = b := fun ha hb he =>
          spec.fc.natCast_inj56 (by unfold natLimit; omega) (by unfold natLimit; omega) (Value.field.inj he)
        have ec0 : m % 256 = c0 := injByte hb0 hc0 he0
        have ec1 : (m / 256) % 256 = c1 := injByte hb1 hc1 he1
        have ec2 : (m / 65536) % 256 = c2 := injByte hb2 hc2 he2
        have ec3 : (m / 16777216) % 256 = c3 := injByte hb3 hc3 he3
        subst ec0; subst ec1; subst ec2; subst ec3
        have hpack : n % U32.base =
            U32.pack (m % 256) ((m / 256) % 256) ((m / 65536) % 256) ((m / 16777216) % 256) := by
          have hd1 : m / 256 / 256 = m / 65536 := by rw [Nat.div_div_eq_div_mul]
          have hd2 : m / 65536 / 256 = m / 16777216 := by rw [Nat.div_div_eq_div_mul]
          have hd3 : (m / 16777216) % 256 = m / 16777216 := Nat.mod_eq_of_lt (by omega)
          rw [← hmEq]; unfold U32.pack; omega
        rw [← hpack] at hrU32
        exact .call (.cons .literal .nil)
          (by simpa [instanceName, Instance.symbol] using spec.u32_of_field_mk n _ _ hn hrU32)
      · simpa only [foldConstU32OfFieldList, foldConstU32OfField] using ev
    · simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
      rw [map_qualifyExprF] at ev ⊢
      cases ev with | call items hcal =>
        exact .call (evalArgs_foldConstU32OfField_backward spec items) hcal
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_foldConstU32OfField_backward {world : World F} (spec : U32WorldSpec world) :
    ∀ {xs : List Expr} {locals : Environment F Nat} {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs world [] locals ((foldConstU32OfFieldList xs).map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h'
  | [], _, _, _, _, ev => by cases ev; exact .nil
  | x :: xs, _, _, _, _, ev => by
    cases ev with
    | cons hd tl =>
      exact .cons
        (evalExpr_foldConstU32OfField_backward spec hd)
        (evalArgs_foldConstU32OfField_backward spec tl)
termination_by xs => sizeOf xs

end

end FoldConstEval

end FoldConstU32

/-! ## Section 5: `flattenLets` Backward Soundness -/

section FlattenLetsProof

theorem hasFreeVar_not_in_pat {v : String} {p : Pat} {e : Expr}
    (h : (patBoundVars p).all (fun u => !hasFreeVar u e) = true) (hv : hasFreeVar v e = true) :
    v ∉ patBoundVars p := by
  intro hmem
  have h1 := List.all_eq_true.mp h v hmem
  simp [hv] at h1

theorem lookup_append_of_not_mem {Δ Γ : TyEnv} {x : String} (h : x ∉ Δ.map Prod.fst) :
    (Δ ++ Γ).lookup x = Γ.lookup x := by
  induction Δ with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨nm, ty⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, List.lookup, beq_false_of_ne h.1]
    exact ih h.2

theorem find?_append_of_not_mem {F : Type} {bs locals : Environment F Nat} {x : String}
    (h : x ∉ bs.map Prod.fst) :
    (bs ++ locals).find? (·.1 == x) = locals.find? (·.1 == x) := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨nm, v⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, List.find?_cons, beq_false_of_ne (Ne.symm h.1)]
    exact ih h.2

private theorem flattenLetsList_length (fuel : Nat) :
    ∀ (xs : List Expr), (flattenLetsList fuel xs).length = xs.length
  | [] => by simp [flattenLetsList]
  | _ :: xs => by simp [flattenLetsList, flattenLetsList_length fuel xs]

private theorem flattenLetsArms_eq_map (fuel : Nat) (arms : List (Pat × Expr)) :
    flattenLetsArms fuel arms = arms.map fun arm => (arm.1, flattenLets fuel arm.2) := by
  induction arms with
  | nil => simp [flattenLetsArms]
  | cons a tl ih => rcases a with ⟨p, b⟩; simp [flattenLetsArms, ih]

private theorem flattenLets_letValue_other (fuel : Nat) (p : Pat) (x body : Expr)
    (hx : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1) :
    flattenLets fuel (.letValue p x body) =
      .letValue p (flattenLets fuel x) (flattenLets fuel body) := by
  cases x <;> first | exact absurd rfl (hx _ _ _) | simp only [flattenLets]

private theorem qualifyExprF_letValue (F : Type) [Field F] (p : Pat) (x b : Expr) :
    qualifyExprF F (.letValue p x b) =
      .letValue (qualifyPatF F p) (qualifyExprF F x) (qualifyExprF F b) := by
  simp [qualifyExprF, qualifyPatF, qualifyExpr, Aiur.Generic.Expr.map]

mutual

/-- `flattenLets` preserves `HasTy`. -/
theorem hasTy_flattenLets {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ (fuel : Nat) {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy sigs enums Γ e t →
      HasTy sigs enums Γ (flattenLets fuel e) t
  | _, _, _, _, .literal => by simp only [flattenLets]; exact .literal
  | _, _, _, _, .var hl => by simp only [flattenLets]; exact .var hl
  | fuel, _, _, _, .tuple items => by
    simp only [flattenLets]; exact .tuple (hasTy_flattenLetsList fuel items)
  | fuel, _, _, _, .array hlen items => by
    simp only [flattenLets]
    exact .array (by rw [flattenLetsList_length]; exact hlen) (hasTy_flattenLetsList fuel items)
  | fuel, _, _, _, .repeat hx => by simp only [flattenLets]; exact .repeat (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .index hx => by simp only [flattenLets]; exact .index (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .project hx hget => by
    simp only [flattenLets]; exact .project (hasTy_flattenLets fuel hx) hget
  | fuel, _, _, _, .slice hnot hx => by
    simp only [flattenLets]; exact .slice hnot (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .construct h1 h2 h3 h4 hctor items => by
    simp only [flattenLets]; exact .construct h1 h2 h3 h4 hctor (hasTy_flattenLetsList fuel items)
  | fuel, _, _, _, .builtin items => by
    simp only [flattenLets]; exact .builtin (hasTy_flattenLetsList fuel items)
  | fuel, _, _, _, .store hx => by simp only [flattenLets]; exact .store (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .load hx => by simp only [flattenLets]; exact .load (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .hint hfo hx => by
    simp only [flattenLets]; exact .hint hfo (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .neg hx => by simp only [flattenLets]; exact .neg (hasTy_flattenLets fuel hx)
  | fuel, _, _, _, .binary hl hr => by
    simp only [flattenLets]; exact .binary (hasTy_flattenLets fuel hl) (hasTy_flattenLets fuel hr)
  | fuel, _, _, _, .call hsig items => by
    simp only [flattenLets]; exact .call hsig (hasTy_flattenLetsList fuel items)
  | fuel, _, _, _, .matchValue hs harms => by
    simp only [flattenLets]
    exact .matchValue (hasTy_flattenLets fuel hs) (hasTy_flattenLetsArms fuel harms)
  | fuel, Γ, _, tb, .letValue (p := p) (x := x) (b := body) (Δ := Δ) hx hp hb => by
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      cases fuel with
      | zero =>
        rw [flattenLets]
        exact .letValue (hasTy_flattenLets 0 hx) hp (hasTy_flattenLets 0 hb)
      | succ fuel' =>
        rw [flattenLets]
        split
        · next hfresh =>
          cases hx with
          | letValue hrhs1 hp1 hbody1 =>
            rename_i Δ1
            have hbody' : HasTy sigs enums (Δ ++ (Δ1 ++ Γ)) body tb := by
              refine hasTy_envAgree hb fun z hz => ?_
              refine lookup_append_agree fun _ => ?_
              have hnot1 : z ∉ Δ1.map Prod.fst := by
                rw [hp1.dom_eq]
                exact hasFreeVar_not_in_pat hfresh hz
              exact (lookup_append_of_not_mem hnot1).symm
            exact hasTy_flattenLets fuel' (.letValue hrhs1 hp1 (.letValue hbody1 hp hbody'))
        · exact .letValue (hasTy_flattenLets (fuel' + 1) hx) hp (hasTy_flattenLets (fuel' + 1) hb)
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun p1 rhs1 body1 heq =>
        hlet ⟨p1, rhs1, body1, heq⟩
      rw [flattenLets_letValue_other fuel p x body hnot]
      exact .letValue (hasTy_flattenLets fuel hx) hp (hasTy_flattenLets fuel hb)
termination_by fuel _ e _ _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec]
  all_goals omega

theorem hasTy_flattenLetsList {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ (fuel : Nat) {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList sigs enums Γ xs ts →
      HasTyList sigs enums Γ (flattenLetsList fuel xs) ts
  | _, _, _, _, .nil => by simp only [flattenLetsList]; exact .nil
  | fuel, _, _, _, .cons hd tl => by
    simp only [flattenLetsList]
    exact .cons (hasTy_flattenLets fuel hd) (hasTy_flattenLetsList fuel tl)
termination_by fuel _ xs _ _ => (fuel, sizeOf xs)

theorem hasTy_flattenLetsArms {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ (fuel : Nat) {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms sigs enums Γ ts arms tb →
      HasTyArms sigs enums Γ ts (flattenLetsArms fuel arms) tb
  | _, _, _, _, _, .nil => by simp only [flattenLetsArms]; exact .nil
  | fuel, _, _, _, _, .cons hp hb tl => by
    simp only [flattenLetsArms]
    exact .cons hp (hasTy_flattenLets fuel hb) (hasTy_flattenLetsArms fuel tl)
termination_by fuel _ _ _ arms _ => (fuel, sizeOf arms)

end

section FlattenEval

variable {F : Type} [Field F] [DecidableEq F]

mutual

/-- **Stage 4 (`flattenLets`) Same-World Backward Soundness:**
Hoisting nested `let p := (let p1 := rhs1; body1); body` → `let p1 := rhs1; let p := body1; body`
when `p1`'s binders are not free in `body` preserves `EvalExpr` backward! -/
theorem evalExpr_flattenLets_backward {world : World F} :
    ∀ (fuel : Nat) {e : Expr} {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      isCleanExpr e = true →
      EvalExpr world [] locals (qualifyExprF F (flattenLets fuel e)) h r h' →
      EvalExpr world [] locals (qualifyExprF F e) h r h'
  | _, .control .., _, _, _, _, hc, _ | _, .global .., _, _, _, _, hc, _ => by
    simp [isCleanExpr] at hc
  | _, .literal _, _, _, _, _, _, ev | _, .var _, _, _, _, _, _, ev => by
    simpa only [flattenLets] using ev
  | fuel, .tuple xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple items => exact .tuple (evalArgs_flattenLets_backward fuel hc items)
  | fuel, .array xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array items => exact .array (evalArgs_flattenLets_backward fuel hc items)
  | fuel, .construct ty targs nm xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct items => exact .construct (evalArgs_flattenLets_backward fuel hc items)
  | fuel, .constructAs ps ty nm xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | constructAs items => exact .constructAs (evalArgs_flattenLets_backward fuel hc items)
  | fuel, .record hd xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | record items => exact .record (evalArgs_flattenLets_backward fuel hc items)
  | fuel, .update ps xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | update items ha => exact .update (evalArgs_flattenLets_backward fuel hc items) ha
  | fuel, .builtin op xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin items ha => exact .builtin (evalArgs_flattenLets_backward fuel hc items) ha
  | fuel, .call nm targs xs, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | call items hcal => exact .call (evalArgs_flattenLets_backward fuel hc items) hcal
  | fuel, .repeat x n, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item => exact .repeat (evalExpr_flattenLets_backward fuel hc item)
  | fuel, .index x i, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp => exact .index (evalExpr_flattenLets_backward fuel hc item) hp
  | fuel, .slice x a b, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs => exact .slice (evalExpr_flattenLets_backward fuel hc item) hs
  | fuel, .member x f, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | member item hp => exact .member (evalExpr_flattenLets_backward fuel hc item) hp
  | fuel, .project x i, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp => exact .project (evalExpr_flattenLets_backward fuel hc item) hp
  | fuel, .store x, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item => exact .store (evalExpr_flattenLets_backward fuel hc item)
  | fuel, .load x, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl => exact .load (evalExpr_flattenLets_backward fuel hc item) hl
  | fuel, .hint ty x ch, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht => exact .hint (evalExpr_flattenLets_backward fuel (e := x) hc item) ht
  | fuel, .neg x, _, _, _, _, hc, ev => by
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop => exact .neg (evalExpr_flattenLets_backward fuel hc item) hop
  | fuel, .binary op l r, _, _, _, _, hc, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary el er hop =>
      exact .binary
        (evalExpr_flattenLets_backward fuel hc.1 el)
        (evalExpr_flattenLets_backward fuel hc.2 er) hop
  | fuel, .matchValue s arms, _, _, _, _, hc, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [flattenLets, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | matchValue evS hsel evB =>
      rw [map_qualifyArmsF, flattenLetsArms_eq_map, List.map_map] at hsel
      have hsel' : SourceSemantics.selectArm world [] _ _
          (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F (flattenLets fuel arm.2))) =
          .ok (some (_, _)) := hsel
      obtain ⟨p, b, hmem, rfl, _, hselOrig⟩ :=
        selectArm_mapBody (fun _ b => flattenLets fuel b) hsel'
      have hcb := ((isCleanArms_iff.mp hc.2) (p, b) hmem).2
      rw [← map_qualifyArmsF] at hselOrig
      exact .matchValue
        (evalExpr_flattenLets_backward fuel hc.1 evS)
        hselOrig
        (evalExpr_flattenLets_backward fuel hcb evB)
  | fuel, .letValue p x body, _, _, _, _, hc, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    obtain ⟨⟨hp, hx⟩, hb⟩ := hc
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      simp only [isCleanExpr, Bool.and_eq_true] at hx
      obtain ⟨⟨hp1, hrhs1⟩, hbody1⟩ := hx
      have hxc : isCleanExpr (.letValue p1 rhs1 body1) = true := by
        simp [isCleanExpr, hp1, hrhs1, hbody1]
      cases fuel with
      | zero =>
        rw [flattenLets] at ev
        rw [qualifyExprF_letValue] at ev ⊢
        cases ev with
        | letValue evX hm evB =>
          exact .letValue
            (evalExpr_flattenLets_backward 0 hxc evX) hm
            (evalExpr_flattenLets_backward 0 hb evB)
      | succ fuel' =>
        rw [flattenLets] at ev
        split at ev
        · next hfresh =>
          have hcHoist : isCleanExpr (.letValue p1 rhs1 (.letValue p body1 body)) = true := by
            simp [isCleanExpr, hp1, hrhs1, hp, hbody1, hb]
          have evHoist := evalExpr_flattenLets_backward fuel' hcHoist ev
          rw [qualifyExprF_letValue, qualifyExprF_letValue] at evHoist ⊢
          cases evHoist with
          | letValue evRhs1 hm1 evInner =>
            rename_i _ _ bs1
            cases evInner with
            | letValue evBody1 hm evBody =>
              have hnames1 := matchPattern_names_of_simple hp1 hm1
              refine .letValue (.letValue evRhs1 hm1 evBody1) hm ?_
              refine evalExpr_localsAgree hb ?_ evBody
              intro z hz
              refine find?_append_agree fun _ => ?_
              have hnot1 : z ∉ bs1.map Prod.fst := by
                rw [hnames1]
                exact hasFreeVar_not_in_pat hfresh hz
              exact find?_append_of_not_mem hnot1
        · rw [qualifyExprF_letValue] at ev ⊢
          cases ev with
          | letValue evX hm evB =>
            exact .letValue
              (evalExpr_flattenLets_backward (fuel' + 1) hxc evX) hm
              (evalExpr_flattenLets_backward (fuel' + 1) hb evB)
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun p1 rhs1 body1 heq =>
        hlet ⟨p1, rhs1, body1, heq⟩
      rw [flattenLets_letValue_other fuel p x body hnot] at ev
      rw [qualifyExprF_letValue] at ev ⊢
      cases ev with
      | letValue evX hm evB =>
        exact .letValue
          (evalExpr_flattenLets_backward fuel hx evX) hm
          (evalExpr_flattenLets_backward fuel hb evB)
termination_by fuel e _ _ _ _ _ _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec]
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_flattenLets_backward {world : World F} :
    ∀ (fuel : Nat) {xs : List Expr} {locals : Environment F Nat} {h h' : Heap F} {vs : List (SourceValue F)},
      isCleanList xs = true →
      EvalArgs world [] locals ((flattenLetsList fuel xs).map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h'
  | _, [], _, _, _, _, _, ev => by
    simp only [flattenLetsList, List.map_nil] at ev ⊢
    cases ev; exact .nil
  | fuel, x :: xs, _, _, _, _, hc, ev => by
    simp only [isCleanList, Bool.and_eq_true] at hc
    simp only [flattenLetsList, List.map_cons] at ev ⊢
    cases ev with
    | cons hd tl =>
      exact .cons
        (evalExpr_flattenLets_backward fuel hc.1 hd)
        (evalArgs_flattenLets_backward fuel hc.2 tl)
termination_by fuel xs _ _ _ _ _ _ => (fuel, sizeOf xs)

end

end FlattenEval

end FlattenLetsProof

/-! ## Section 6: `Peephole.rewriteExpr` Full `UInt32` Backward Soundness -/

section PeepholeProof

/-! ### Part 6A: `u32ValOfNat`, `sigsWithU32OfField`, `literalsBounded`, `NoLetShadow`, `ConstEnvOk` -/

/-- Constructive 4-byte `UInt32` `SourceValue F` for any `n < 2^32`. -/
def u32ValOfNat (F : Type) [NatCast F] (n : Nat) : SourceValue F :=
  .tuple [.field ((n % 256 : Nat) : F),
          .field (((n / 256) % 256 : Nat) : F),
          .field (((n / 65536) % 256 : Nat) : F),
          .field (((n / 16777216) % 256 : Nat) : F)]

theorem isU32Val_u32ValOfNat {F : Type} [Field F] {n : Nat} (hn : n < U32.base) :
    isU32Val n (u32ValOfNat F n) := by
  refine ⟨n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256,
    Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega),
    Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), ?_, rfl⟩
  have hd1 : n / 256 / 256 = n / 65536 := by rw [Nat.div_div_eq_div_mul]
  have hd2 : n / 65536 / 256 = n / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have hlt3 : n / 16777216 < 256 := by unfold U32.base at hn; omega
  have hm3 : (n / 16777216) % 256 = n / 16777216 := Nat.mod_eq_of_lt hlt3
  unfold U32.pack U32.base at *; omega

/-- Extend a signature table with the standard signature of `Prog::u32_of_field`,
used internally between `Peephole.fuseExpr` and `foldConstU32OfField`. -/
def sigsWithU32OfField (sigs : FnSigs) : FnSigs :=
  fun qnm => if qnm == qualified "u32_of_field" then some ([.field], u32Ty) else sigs qnm

theorem sigsWithU32OfField_u32_of_field (sigs : FnSigs) :
    sigsWithU32OfField sigs (qualified "u32_of_field") = some ([.field], u32Ty) := by
  simp [sigsWithU32OfField]

theorem sigsWithU32OfField_nonProg (fns : List Fn) {qnm : String} (hnp : isProgQName qnm = false) :
    sigsWithU32OfField (fnSigsOf fns) qnm = libFnSig qnm := by
  have hne : qnm ≠ qualified "u32_of_field" := by
    intro h; subst h; simp [isProgQName_qualified] at hnp
  simp [sigsWithU32OfField, hne, fnSigsOf_nonProg fns hnp]

theorem sigsWithU32OfField_of_ne (sigs : FnSigs) {qnm : String} (hne : qnm ≠ qualified "u32_of_field") :
    sigsWithU32OfField sigs qnm = sigs qnm := by
  simp [sigsWithU32OfField, hne]

mutual

/-- Monotonicity of `HasTy` under pointwise signature table extension. -/
theorem hasTy_mono_sigs {sigs1 sigs2 : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    (hmono : ∀ qnm v, sigs1 qnm = some v → sigs2 qnm = some v) :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy sigs1 enums Γ e t → HasTy sigs2 enums Γ e t
  | _, _, _, .literal => .literal
  | _, _, _, .var hl => .var hl
  | _, _, _, .tuple items => .tuple (hasTyList_mono_sigs hmono items)
  | _, _, _, .array hlen items => .array hlen (hasTyList_mono_sigs hmono items)
  | _, _, _, .repeat hx => .repeat (hasTy_mono_sigs hmono hx)
  | _, _, _, .index hx => .index (hasTy_mono_sigs hmono hx)
  | _, _, _, .project hx hget => .project (hasTy_mono_sigs hmono hx) hget
  | _, _, _, .slice hnot hx => .slice hnot (hasTy_mono_sigs hmono hx)
  | _, _, _, .construct h1 h2 h3 h4 hctor items =>
    .construct h1 h2 h3 h4 hctor (hasTyList_mono_sigs hmono items)
  | _, _, _, .builtin items => .builtin (hasTyList_mono_sigs hmono items)
  | _, _, _, .store hx => .store (hasTy_mono_sigs hmono hx)
  | _, _, _, .load hx => .load (hasTy_mono_sigs hmono hx)
  | _, _, _, .hint hfo hx => .hint hfo (hasTy_mono_sigs hmono hx)
  | _, _, _, .neg hx => .neg (hasTy_mono_sigs hmono hx)
  | _, _, _, .binary hl hr => .binary (hasTy_mono_sigs hmono hl) (hasTy_mono_sigs hmono hr)
  | _, _, _, .call hsig items => .call (hmono _ _ hsig) (hasTyList_mono_sigs hmono items)
  | _, _, _, .letValue hx hp hb => .letValue (hasTy_mono_sigs hmono hx) hp (hasTy_mono_sigs hmono hb)
  | _, _, _, .matchValue hs harms =>
    .matchValue (hasTy_mono_sigs hmono hs) (hasTyArms_mono_sigs hmono harms)

theorem hasTyList_mono_sigs {sigs1 sigs2 : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    (hmono : ∀ qnm v, sigs1 qnm = some v → sigs2 qnm = some v) :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList sigs1 enums Γ xs ts → HasTyList sigs2 enums Γ xs ts
  | _, _, _, .nil => .nil
  | _, _, _, .cons hd tl => .cons (hasTy_mono_sigs hmono hd) (hasTyList_mono_sigs hmono tl)

theorem hasTyArms_mono_sigs {sigs1 sigs2 : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    (hmono : ∀ qnm v, sigs1 qnm = some v → sigs2 qnm = some v) :
    ∀ {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms sigs1 enums Γ ts arms tb → HasTyArms sigs2 enums Γ ts arms tb
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hp hb tl =>
    .cons hp (hasTy_mono_sigs hmono hb) (hasTyArms_mono_sigs hmono tl)

end

theorem hasTy_to_sigsWithU32OfField {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) {Γ : TyEnv} {e : Expr} {t : Lower.Ty}
    (h : HasTy (fnSigsOf fns) enums Γ e t) :
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t := by
  refine hasTy_mono_sigs ?_ h
  intro qnm v hv
  unfold sigsWithU32OfField
  by_cases hq : qnm = qualified "u32_of_field"
  · subst hq
    simp only [beq_self_eq_true, ↓reduceIte]
    rcases v with ⟨ptys, rty⟩
    obtain ⟨rfl, rfl⟩ := hSigs.1 ptys rty hv
    rfl
  · simp [hq, hv]

theorem qualifyName_of_isShrName {nm : String} (h : Peephole.isShrName nm = true) :
    qualifyName nm = qualified "u32_shr" := by
  simp only [Peephole.isShrName, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> rfl

theorem qualifyName_of_isShlName {nm : String} (h : Peephole.isShlName nm = true) :
    qualifyName nm = qualified "u32_shl" := by
  simp only [Peephole.isShlName, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> rfl

theorem qualifyName_of_isU32OfFieldName {nm : String} (h : Peephole.isU32OfFieldName nm = true) :
    qualifyName nm = qualified "u32_of_field" ∨ qualifyName nm = "UInt32::from_field" := by
  simp only [Peephole.isU32OfFieldName, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem qualifyExprF_call (F : Type) [Field F] (nm : String) (targs : Option (List Lower.Ty))
    (xs : List Expr) :
    qualifyExprF F (.call nm targs xs) =
      .call (qualifyName nm) (targs.map (List.map qualifyTy)) (xs.map (qualifyExprF F)) := by
  simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map_map, Function.comp_def]

theorem qualifyExprF_var (F : Type) [Field F] (x : String) :
    qualifyExprF F (.var x) = .var x := by
  simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]

theorem qualifyExprF_literal (F : Type) [Field F] (n : Nat) :
    qualifyExprF F (.literal n) = .literal (n : F) := by
  simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]

theorem qualifyExprF_array (F : Type) [Field F] (xs : List Expr) :
    qualifyExprF F (.array xs) = .array (xs.map (qualifyExprF F)) := by
  simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map_map, Function.comp_def]

theorem qualifyExprF_index (F : Type) [Field F] (x : Expr) (i : Nat) :
    qualifyExprF F (.index x i) = .index (qualifyExprF F x) i := by
  simp [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]

section ValOkExt

variable {F : Type} [Field F] [DecidableEq F]

/-- `EvalExpr` typing soundness under `sigsWithU32OfField (fnSigsOf fns)`. -/
theorem evalExpr_valOk_ext {world : World F} {enums : List Aiur.Generic.EnumDecl} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns)
    (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world)
    (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns)
    {Γ : TyEnv} {locals : Environment F Nat} {e : Expr} {t : Lower.Ty}
    {h h' : Heap F} {r : SourceValue F}
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t)
    (henv : EnvOk enums h h.length Γ locals)
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ValOk enums h' h'.length t r := by
  obtain ⟨d, evN⟩ := EvalExprN.ofEvalExpr ev
  refine (evalExprN_transfer_typed (SameAuxWorld.refl world) ?_ hty henv evN).2
  intro _ _ qnm ptys rty args h1 r1 h2 hsig hargs cal
  by_cases hq : qnm = qualified "u32_of_field"
  · subst hq
    rw [sigsWithU32OfField_u32_of_field] at hsig
    simp only [Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨rfl, rfl⟩ := hsig
    rcases hargs with _ | ⟨_, _ | _⟩
    obtain ⟨⟨k, _, _, hr⟩, _⟩ := spec.u32_of_field _ _ _ _ cal.toEvalFn
    exact ⟨cal.toEvalFn, (ValOk_u32 ..).mpr ⟨_, hr⟩⟩
  · rw [sigsWithU32OfField_of_ne _ hq] at hsig
    exact ⟨cal.toEvalFn, evalFn_valOk hnd hHas hProv hLib spec hWT hsig hargs cal.toEvalFn⟩

theorem evalArgs_valOk_ext {world : World F} {enums : List Aiur.Generic.EnumDecl} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns)
    (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world)
    (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {xs : List Expr} {ts : List Lower.Ty}
      {h h' : Heap F} {vs : List (SourceValue F)},
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      EnvOk enums h h.length Γ locals →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h' →
      List.Forall₂ (ValOk enums h' h'.length) ts vs
  | _, _, _, _, _, _, _, .nil, _, ev => by cases ev; exact .nil
  | _, _, _, _, _, _, _, .cons hd tl, henv, ev => by
    cases ev with
    | cons evH evT =>
      have hokH := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hd henv evH
      have hext1 := evH.heap_extends
      have hokT := evalArgs_valOk_ext hnd hHas hProv hLib spec hWT tl
        (henv.mono hext1 hext1.length_le) evT
      have hext2 := evT.heap_extends
      exact .cons (hokH.mono hext2 hext2.length_le) hokT

end ValOkExt

mutual

/-- Every `.literal n` occurring anywhere in `e` satisfies `n < bound`. -/
def allLitsLt (bound : Nat) : Expr → Bool
  | .literal n => decide (n < bound)
  | .var _ | .global _ _ => true
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs => allLitsLtList bound xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x => allLitsLt bound x
  | .binary _ l r => allLitsLt bound l && allLitsLt bound r
  | .letValue _ v b => allLitsLt bound v && allLitsLt bound b
  | .matchValue s arms => allLitsLt bound s && allLitsLtArms bound arms

def allLitsLtList (bound : Nat) : List Expr → Bool
  | [] => true
  | x :: xs => allLitsLt bound x && allLitsLtList bound xs

def allLitsLtArms (bound : Nat) : List (Pat × Expr) → Bool
  | [] => true
  | (_, b) :: rest => allLitsLt bound b && allLitsLtArms bound rest

end

theorem allLitsLt_mem_arms {bound : Nat} {arms : List (Pat × Expr)} {p : Pat} {b : Expr}
    (h : allLitsLtArms bound arms = true) (hmem : (p, b) ∈ arms) :
    allLitsLt bound b = true := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    simp only [allLitsLtArms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h.1
    · exact ih h.2 htl

theorem noInlinableCalls_mem_arms {arms : List (Pat × Expr)} {p : Pat} {b : Expr}
    (h : noInlinableCallsArms arms = true) (hmem : (p, b) ∈ arms) :
    noInlinableCalls b = true := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    simp only [noInlinableCallsArms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h.1
    · exact ih h.2 htl

mutual

theorem allLitsLt_flattenLets (bound : Nat) :
    ∀ (fuel : Nat) {e : Expr}, allLitsLt bound e = true → allLitsLt bound (flattenLets fuel e) = true
  | _, .literal _, h => by simpa [flattenLets] using h
  | _, .var _, _ | _, .global _ _, _ => by simp [flattenLets, allLitsLt]
  | _, .control _ _, h => by simpa [flattenLets] using h
  | fuel, .tuple xs, h | fuel, .array xs, h | fuel, .construct _ _ _ xs, h
  | fuel, .constructAs _ _ _ xs, h | fuel, .record _ xs, h | fuel, .update _ xs, h
  | fuel, .builtin _ xs, h | fuel, .call _ _ xs, h => by
    simp only [flattenLets, allLitsLt] at h ⊢; exact allLitsLt_flattenLetsList bound fuel h
  | fuel, .repeat x _, h | fuel, .index x _, h | fuel, .slice x _ _, h
  | fuel, .member x _, h | fuel, .project x _, h | fuel, .store x, h
  | fuel, .load x, h | fuel, .hint _ x _, h | fuel, .neg x, h => by
    simp only [flattenLets, allLitsLt] at h ⊢; exact allLitsLt_flattenLets bound fuel h
  | fuel, .binary _ l r, h => by
    simp only [flattenLets, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_flattenLets bound fuel h.1, allLitsLt_flattenLets bound fuel h.2⟩
  | fuel, .matchValue s arms, h => by
    simp only [flattenLets, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_flattenLets bound fuel h.1, allLitsLt_flattenLetsArms bound fuel h.2⟩
  | fuel, .letValue p x body, h => by
    simp only [allLitsLt, Bool.and_eq_true] at h
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      cases fuel with
      | zero =>
        rw [flattenLets]; simp only [allLitsLt, Bool.and_eq_true]
        exact ⟨allLitsLt_flattenLets bound 0 h.1, allLitsLt_flattenLets bound 0 h.2⟩
      | succ fuel' =>
        rw [flattenLets]; split
        · simp only [allLitsLt, Bool.and_eq_true] at h
          exact allLitsLt_flattenLets bound fuel' (by simp [allLitsLt, h.1.1, h.1.2, h.2])
        · simp only [allLitsLt, Bool.and_eq_true]
          exact ⟨allLitsLt_flattenLets bound (fuel' + 1) h.1, allLitsLt_flattenLets bound (fuel' + 1) h.2⟩
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun a b c he => hlet ⟨a, b, c, he⟩
      rw [flattenLets_letValue_other fuel p x body hnot]
      simp only [allLitsLt, Bool.and_eq_true]
      exact ⟨allLitsLt_flattenLets bound fuel h.1, allLitsLt_flattenLets bound fuel h.2⟩
termination_by fuel e _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec]
  all_goals omega

theorem allLitsLt_flattenLetsList (bound : Nat) :
    ∀ (fuel : Nat) {xs : List Expr},
      allLitsLtList bound xs = true → allLitsLtList bound (flattenLetsList fuel xs) = true
  | _, [], _ => by simp [flattenLetsList, allLitsLtList]
  | fuel, x :: xs, h => by
    simp only [flattenLetsList, allLitsLtList, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_flattenLets bound fuel h.1, allLitsLt_flattenLetsList bound fuel h.2⟩
termination_by fuel xs _ => (fuel, sizeOf xs)

theorem allLitsLt_flattenLetsArms (bound : Nat) :
    ∀ (fuel : Nat) {arms : List (Pat × Expr)},
      allLitsLtArms bound arms = true → allLitsLtArms bound (flattenLetsArms fuel arms) = true
  | _, [], _ => by simp [flattenLetsArms, allLitsLtArms]
  | fuel, (p, b) :: rest, h => by
    simp only [flattenLetsArms, allLitsLtArms, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_flattenLets bound fuel h.1, allLitsLt_flattenLetsArms bound fuel h.2⟩
termination_by fuel arms _ => (fuel, sizeOf arms)

end

mutual

theorem noInlinableCalls_flattenLets :
    ∀ (fuel : Nat) {e : Expr}, noInlinableCalls e = true → noInlinableCalls (flattenLets fuel e) = true
  | _, .literal _, _ | _, .var _, _ | _, .global _ _, _ => by simp [flattenLets, noInlinableCalls]
  | _, .control _ _, h => by simpa [flattenLets] using h
  | fuel, .tuple xs, h | fuel, .array xs, h | fuel, .construct _ _ _ xs, h
  | fuel, .constructAs _ _ _ xs, h | fuel, .record _ xs, h | fuel, .update _ xs, h
  | fuel, .builtin _ xs, h => by
    simp only [flattenLets, noInlinableCalls] at h ⊢; exact noInlinableCalls_flattenLetsList fuel h
  | fuel, .call _ _ xs, h => by
    simp only [flattenLets, noInlinableCalls, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, noInlinableCalls_flattenLetsList fuel h.2⟩
  | fuel, .repeat x _, h | fuel, .index x _, h | fuel, .slice x _ _, h
  | fuel, .member x _, h | fuel, .project x _, h | fuel, .store x, h
  | fuel, .load x, h | fuel, .hint _ x _, h | fuel, .neg x, h => by
    simp only [flattenLets, noInlinableCalls] at h ⊢; exact noInlinableCalls_flattenLets fuel h
  | fuel, .binary _ l r, h => by
    simp only [flattenLets, noInlinableCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_flattenLets fuel h.1, noInlinableCalls_flattenLets fuel h.2⟩
  | fuel, .matchValue s arms, h => by
    simp only [flattenLets, noInlinableCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_flattenLets fuel h.1, noInlinableCalls_flattenLetsArms fuel h.2⟩
  | fuel, .letValue p x body, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      cases fuel with
      | zero =>
        rw [flattenLets]; simp only [noInlinableCalls, Bool.and_eq_true]
        exact ⟨noInlinableCalls_flattenLets 0 h.1, noInlinableCalls_flattenLets 0 h.2⟩
      | succ fuel' =>
        rw [flattenLets]; split
        · simp only [noInlinableCalls, Bool.and_eq_true] at h
          exact noInlinableCalls_flattenLets fuel' (by simp [noInlinableCalls, h.1.1, h.1.2, h.2])
        · simp only [noInlinableCalls, Bool.and_eq_true]
          exact ⟨noInlinableCalls_flattenLets (fuel' + 1) h.1, noInlinableCalls_flattenLets (fuel' + 1) h.2⟩
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun a b c he => hlet ⟨a, b, c, he⟩
      rw [flattenLets_letValue_other fuel p x body hnot]
      simp only [noInlinableCalls, Bool.and_eq_true]
      exact ⟨noInlinableCalls_flattenLets fuel h.1, noInlinableCalls_flattenLets fuel h.2⟩
termination_by fuel e _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec]
  all_goals omega

theorem noInlinableCalls_flattenLetsList :
    ∀ (fuel : Nat) {xs : List Expr},
      noInlinableCallsList xs = true → noInlinableCallsList (flattenLetsList fuel xs) = true
  | _, [], _ => by simp [flattenLetsList, noInlinableCallsList]
  | fuel, x :: xs, h => by
    simp only [flattenLetsList, noInlinableCallsList, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_flattenLets fuel h.1, noInlinableCalls_flattenLetsList fuel h.2⟩
termination_by fuel xs _ => (fuel, sizeOf xs)

theorem noInlinableCalls_flattenLetsArms :
    ∀ (fuel : Nat) {arms : List (Pat × Expr)},
      noInlinableCallsArms arms = true → noInlinableCallsArms (flattenLetsArms fuel arms) = true
  | _, [], _ => by simp [flattenLetsArms, noInlinableCallsArms]
  | fuel, (p, b) :: rest, h => by
    simp only [flattenLetsArms, noInlinableCallsArms, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_flattenLets fuel h.1, noInlinableCalls_flattenLetsArms fuel h.2⟩
termination_by fuel arms _ => (fuel, sizeOf arms)

end

mutual

/-- Every argument to `u32_of_field` has all literals `< 2^56` (`natLimit`), and every
argument to `UInt32::from_field` has all literals `< 2^32` (`U32.base`). Guaranteed on all
`TypedLower` outputs and preserved purely syntactically by every `InlineFuse` + `Peephole` pass! -/
def literalsBounded : Expr → Bool
  | .call nm (some []) [arg] =>
    if nm == "u32_of_field" || nm == "Prog::u32_of_field" then
      allLitsLt natLimit arg && literalsBounded arg
    else if nm == "UInt32::from_field" then
      allLitsLt U32.base arg && literalsBounded arg
    else literalsBounded arg
  | .call _ _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => literalsBoundedList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x => literalsBounded x
  | .binary _ l r => literalsBounded l && literalsBounded r
  | .letValue _ v b => literalsBounded v && literalsBounded b
  | .matchValue s arms => literalsBounded s && literalsBoundedArms arms
  | .literal _ | .var _ | .global _ _ => true

def literalsBoundedList : List Expr → Bool
  | [] => true
  | x :: xs => literalsBounded x && literalsBoundedList xs

def literalsBoundedArms : List (Pat × Expr) → Bool
  | [] => true
  | (_, b) :: rest => literalsBounded b && literalsBoundedArms rest

end

theorem literalsBounded_mem_arms {arms : List (Pat × Expr)} {p : Pat} {b : Expr}
    (h : literalsBoundedArms arms = true) (hmem : (p, b) ∈ arms) :
    literalsBounded b = true := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    simp only [literalsBoundedArms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h.1
    · exact ih h.2 htl

theorem literalsBounded_call_args {nm : String} {targs : Option (List Lower.Ty)} {xs : List Expr}
    (h : literalsBounded (.call nm targs xs) = true) :
    literalsBoundedList xs = true := by
  cases targs with
  | none => simpa [literalsBounded] using h
  | some ts =>
    cases ts with
    | cons _ _ => simpa [literalsBounded] using h
    | nil =>
      cases xs with
      | nil => rfl
      | cons x rest =>
        cases rest with
        | cons _ _ => simpa [literalsBounded] using h
        | nil =>
          simp only [literalsBounded] at h
          simp only [literalsBoundedList, Bool.and_true]
          split at h
          · exact (Bool.and_eq_true _ _ |>.mp h).2
          · split at h
            · exact (Bool.and_eq_true _ _ |>.mp h).2
            · exact h

mutual

theorem literalsBounded_flattenLets :
    ∀ (fuel : Nat) {e : Expr}, literalsBounded e = true → literalsBounded (flattenLets fuel e) = true
  | _, .literal _, _ | _, .var _, _ | _, .global _ _, _ => by simp [flattenLets, literalsBounded]
  | _, .control _ _, h => by simpa [flattenLets] using h
  | fuel, .tuple xs, h | fuel, .array xs, h | fuel, .construct _ _ _ xs, h
  | fuel, .constructAs _ _ _ xs, h | fuel, .record _ xs, h | fuel, .update _ xs, h
  | fuel, .builtin _ xs, h => by
    simp only [flattenLets, literalsBounded] at h ⊢; exact literalsBounded_flattenLetsList fuel h
  | fuel, .call nm targs xs, h => by
    cases targs with
    | none =>
      simp only [flattenLets, literalsBounded] at h ⊢; exact literalsBounded_flattenLetsList fuel h
    | some ts =>
      cases ts with
      | cons _ _ =>
        simp only [flattenLets, literalsBounded] at h ⊢; exact literalsBounded_flattenLetsList fuel h
      | nil =>
        cases xs with
        | nil => simp [flattenLets, flattenLetsList, literalsBounded, literalsBoundedList]
        | cons x rest =>
          cases rest with
          | cons y rest2 =>
            simp only [flattenLets, flattenLetsList, literalsBounded, literalsBoundedList,
              Bool.and_eq_true] at h ⊢
            exact ⟨literalsBounded_flattenLets fuel h.1,
              literalsBounded_flattenLets fuel h.2.1,
              literalsBounded_flattenLetsList fuel h.2.2⟩
          | nil =>
            simp only [flattenLets, flattenLetsList, literalsBounded] at h ⊢
            cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
            | true =>
              simp only [h1, ↓reduceIte, Bool.and_eq_true] at h ⊢
              exact ⟨allLitsLt_flattenLets natLimit fuel h.1, literalsBounded_flattenLets fuel h.2⟩
            | false =>
              simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases h2 : (nm == "UInt32::from_field") with
              | true =>
                simp only [h2, ↓reduceIte, Bool.and_eq_true] at h ⊢
                exact ⟨allLitsLt_flattenLets U32.base fuel h.1, literalsBounded_flattenLets fuel h.2⟩
              | false =>
                simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
                exact literalsBounded_flattenLets fuel h
  | fuel, .repeat x _, h | fuel, .index x _, h | fuel, .slice x _ _, h
  | fuel, .member x _, h | fuel, .project x _, h | fuel, .store x, h
  | fuel, .load x, h | fuel, .hint _ x _, h | fuel, .neg x, h => by
    simp only [flattenLets, literalsBounded] at h ⊢; exact literalsBounded_flattenLets fuel h
  | fuel, .binary _ l r, h => by
    simp only [flattenLets, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_flattenLets fuel h.1, literalsBounded_flattenLets fuel h.2⟩
  | fuel, .matchValue s arms, h => by
    simp only [flattenLets, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_flattenLets fuel h.1, literalsBounded_flattenLetsArms fuel h.2⟩
  | fuel, .letValue p x body, h => by
    simp only [literalsBounded, Bool.and_eq_true] at h
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      cases fuel with
      | zero =>
        rw [flattenLets]; simp only [literalsBounded, Bool.and_eq_true]
        exact ⟨literalsBounded_flattenLets 0 h.1, literalsBounded_flattenLets 0 h.2⟩
      | succ fuel' =>
        rw [flattenLets]; split
        · simp only [literalsBounded, Bool.and_eq_true] at h
          exact literalsBounded_flattenLets fuel' (by simp [literalsBounded, h.1.1, h.1.2, h.2])
        · simp only [literalsBounded, Bool.and_eq_true]
          exact ⟨literalsBounded_flattenLets (fuel' + 1) h.1, literalsBounded_flattenLets (fuel' + 1) h.2⟩
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun a b c he => hlet ⟨a, b, c, he⟩
      rw [flattenLets_letValue_other fuel p x body hnot]
      simp only [literalsBounded, Bool.and_eq_true]
      exact ⟨literalsBounded_flattenLets fuel h.1, literalsBounded_flattenLets fuel h.2⟩
termination_by fuel e _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec, List.cons.sizeOf_spec]
  all_goals omega

theorem literalsBounded_flattenLetsList :
    ∀ (fuel : Nat) {xs : List Expr},
      literalsBoundedList xs = true → literalsBoundedList (flattenLetsList fuel xs) = true
  | _, [], _ => by simp [flattenLetsList, literalsBoundedList]
  | fuel, x :: xs, h => by
    simp only [flattenLetsList, literalsBoundedList, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_flattenLets fuel h.1, literalsBounded_flattenLetsList fuel h.2⟩
termination_by fuel xs _ => (fuel, sizeOf xs)

theorem literalsBounded_flattenLetsArms :
    ∀ (fuel : Nat) {arms : List (Pat × Expr)},
      literalsBoundedArms arms = true → literalsBoundedArms (flattenLetsArms fuel arms) = true
  | _, [], _ => by simp [flattenLetsArms, literalsBoundedArms]
  | fuel, (p, b) :: rest, h => by
    simp only [flattenLetsArms, literalsBoundedArms, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_flattenLets fuel h.1, literalsBounded_flattenLetsArms fuel h.2⟩
termination_by fuel arms _ => (fuel, sizeOf arms)

end

mutual

/-- Non-shadowing / disjoint-let-RHS structural invariant:
no binder in `e` rebinds any name in `scope`, and sibling/let-RHS subexpressions have
disjoint bound variables. Preserved across `inlineCallsM`, `simpExpr`, and `flattenLets`,
and ensures `Peephole.fuseExpr`'s `ConstEnv` is never shadowed inside ANF let-chains. -/
def NoLetShadow (scope : List String) : Expr → Prop
  | .literal _ | .var _ | .global _ _ | .control _ _ => True
  | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs | .call _ _ xs =>
    NoLetShadowList scope xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x => NoLetShadow scope x
  | .binary _ l r =>
    (∀ v, hasBoundVar v l = true → hasBoundVar v r = false) ∧
    NoLetShadow scope l ∧ NoLetShadow scope r
  | .letValue p x b =>
    (∀ v ∈ patBoundVars p, v ∉ scope) ∧
    (∀ v, hasBoundVar v x = true → v ∉ patBoundVars p ∧ hasBoundVar v b = false) ∧
    NoLetShadow scope x ∧ NoLetShadow (patBoundVars p ++ scope) b
  | .matchValue s arms =>
    NoLetShadow scope s ∧ NoLetShadowArms scope arms

def NoLetShadowList (scope : List String) : List Expr → Prop
  | [] => True
  | x :: xs =>
    (∀ v, hasBoundVar v x = true → hasBoundVarList v xs = false) ∧
    NoLetShadow scope x ∧ NoLetShadowList scope xs

def NoLetShadowArms (scope : List String) : List (Pat × Expr) → Prop
  | [] => True
  | (p, b) :: rest =>
    (∀ v ∈ patBoundVars p, v ∉ scope) ∧
    NoLetShadow (patBoundVars p ++ scope) b ∧
    NoLetShadowArms scope rest

end

mutual

/-- Shrinking `scope` (or replacing it by any list containing no bound variables of `e`)
preserves `NoLetShadow`. -/
theorem noLetShadow_scope_imp :
    ∀ {s1 s2 : List String} {e : Expr},
      (∀ v, v ∈ s2 → v ∈ s1 ∨ hasBoundVar v e = false) →
      NoLetShadow s1 e → NoLetShadow s2 e
  | _, _, .literal _, _, _ | _, _, .var _, _, _ | _, _, .global _ _, _, _ | _, _, .control _ _, _, _ => trivial
  | _, _, .tuple xs, hsub, h | _, _, .array xs, hsub, h | _, _, .construct _ _ _ xs, hsub, h
  | _, _, .constructAs _ _ _ xs, hsub, h | _, _, .record _ xs, hsub, h | _, _, .update _ xs, hsub, h
  | _, _, .builtin _ xs, hsub, h | _, _, .call _ _ xs, hsub, h =>
    noLetShadowList_scope_imp hsub h
  | _, _, .repeat x _, hsub, h | _, _, .index x _, hsub, h | _, _, .slice x _ _, hsub, h
  | _, _, .member x _, hsub, h | _, _, .project x _, hsub, h | _, _, .store x, hsub, h
  | _, _, .load x, hsub, h | _, _, .hint _ x _, hsub, h | _, _, .neg x, hsub, h =>
    noLetShadow_scope_imp (e := x) hsub h
  | _, _, .binary _ l r, hsub, ⟨hdisj, hl, hr⟩ => by
    refine ⟨hdisj,
      noLetShadow_scope_imp (fun v hv => ?_) hl,
      noLetShadow_scope_imp (fun v hv => ?_) hr⟩
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2; exact Or.inr h2.1
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2; exact Or.inr h2.2
  | _, _, .letValue p x b, hsub, ⟨hp, hdisj, hx, hb⟩ => by
    refine ⟨fun v hvp hvs2 => ?_, hdisj,
      noLetShadow_scope_imp (fun v hv => ?_) hx,
      noLetShadow_scope_imp (fun v hv => ?_) hb⟩
    · rcases hsub v hvs2 with h1 | h2
      · exact hp v hvp h1
      · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2
        have : (patBoundVars p).contains v = true := List.contains_iff_mem.mpr hvp
        rw [this] at h2; cases h2.1.1
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2; exact Or.inr h2.1.2
    · rcases List.mem_append.mp hv with hvp | hvs2
      · exact Or.inl (List.mem_append_left _ hvp)
      · rcases hsub v hvs2 with h1 | h2
        · exact Or.inl (List.mem_append_right _ h1)
        · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2; exact Or.inr h2.2
  | _, _, .matchValue s arms, hsub, ⟨hs, harms⟩ => by
    refine ⟨noLetShadow_scope_imp (fun v hv => ?_) hs,
      noLetShadowArms_scope_imp (fun v hv => ?_) harms⟩
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2; exact Or.inr h2.1
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVar, Bool.or_eq_false_iff] at h2; exact Or.inr h2.2
termination_by _ _ e _ _ => sizeOf e

theorem noLetShadowList_scope_imp :
    ∀ {s1 s2 : List String} {xs : List Expr},
      (∀ v, v ∈ s2 → v ∈ s1 ∨ hasBoundVarList v xs = false) →
      NoLetShadowList s1 xs → NoLetShadowList s2 xs
  | _, _, [], _, _ => trivial
  | _, _, x :: xs, hsub, ⟨hdisj, hx, hxs⟩ => by
    refine ⟨hdisj,
      noLetShadow_scope_imp (fun v hv => ?_) hx,
      noLetShadowList_scope_imp (fun v hv => ?_) hxs⟩
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVarList, Bool.or_eq_false_iff] at h2; exact Or.inr h2.1
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVarList, Bool.or_eq_false_iff] at h2; exact Or.inr h2.2
termination_by _ _ xs _ _ => sizeOf xs

theorem noLetShadowArms_scope_imp :
    ∀ {s1 s2 : List String} {arms : List (Pat × Expr)},
      (∀ v, v ∈ s2 → v ∈ s1 ∨ hasBoundVarArms v arms = false) →
      NoLetShadowArms s1 arms → NoLetShadowArms s2 arms
  | _, _, [], _, _ => trivial
  | _, _, (p, b) :: rest, hsub, ⟨hp, hb, hrest⟩ => by
    refine ⟨fun v hvp hvs2 => ?_,
      noLetShadow_scope_imp (fun v hv => ?_) hb,
      noLetShadowArms_scope_imp (fun v hv => ?_) hrest⟩
    · rcases hsub v hvs2 with h1 | h2
      · exact hp v hvp h1
      · simp only [hasBoundVarArms, Bool.or_eq_false_iff] at h2
        have : (patBoundVars p).contains v = true := List.contains_iff_mem.mpr hvp
        rw [this] at h2; cases h2.1.1
    · rcases List.mem_append.mp hv with hvp | hvs2
      · exact Or.inl (List.mem_append_left _ hvp)
      · rcases hsub v hvs2 with h1 | h2
        · exact Or.inl (List.mem_append_right _ h1)
        · simp only [hasBoundVarArms, Bool.or_eq_false_iff] at h2; exact Or.inr h2.1.2
    · rcases hsub v hv with h1 | h2
      · exact Or.inl h1
      · simp only [hasBoundVarArms, Bool.or_eq_false_iff] at h2; exact Or.inr h2.2
termination_by _ _ arms _ _ => sizeOf arms

end

mutual

/-- `NoLetShadow scope e` guarantees no variable in `scope` is bound anywhere inside `e`. -/
theorem noLetShadow_implies_noBoundVar :
    ∀ {scope : List String} {e : Expr},
      NoLetShadow scope e → ∀ v ∈ scope, hasBoundVar v e = false
  | _, .literal _, _, _, _ | _, .var _, _, _, _ | _, .global _ _, _, _, _ | _, .control _ _, _, _, _ => rfl
  | _, .tuple xs, h, v, hv | _, .array xs, h, v, hv | _, .construct _ _ _ xs, h, v, hv
  | _, .constructAs _ _ _ xs, h, v, hv | _, .record _ xs, h, v, hv | _, .update _ xs, h, v, hv
  | _, .builtin _ xs, h, v, hv | _, .call _ _ xs, h, v, hv =>
    noLetShadowList_implies_noBoundVar h v hv
  | _, .repeat x _, h, v, hv | _, .index x _, h, v, hv | _, .slice x _ _, h, v, hv
  | _, .member x _, h, v, hv | _, .project x _, h, v, hv | _, .store x, h, v, hv
  | _, .load x, h, v, hv | _, .hint _ x _, h, v, hv | _, .neg x, h, v, hv =>
    noLetShadow_implies_noBoundVar (e := x) h v hv
  | _, .binary _ l r, ⟨_, hl, hr⟩, v, hv => by
    simp [hasBoundVar, noLetShadow_implies_noBoundVar hl v hv, noLetShadow_implies_noBoundVar hr v hv]
  | _, .letValue p x b, ⟨hp, _, hx, hb⟩, v, hv => by
    simp [hasBoundVar, noLetShadow_implies_noBoundVar hx v hv,
      noLetShadow_implies_noBoundVar hb v (List.mem_append_right _ hv)]
    exact fun hmem => hp v hmem hv
  | _, .matchValue s arms, ⟨hs, harms⟩, v, hv => by
    simp [hasBoundVar, noLetShadow_implies_noBoundVar hs v hv,
      noLetShadowArms_implies_noBoundVar harms v hv]
termination_by _ e _ _ _ => sizeOf e

theorem noLetShadowList_implies_noBoundVar :
    ∀ {scope : List String} {xs : List Expr},
      NoLetShadowList scope xs → ∀ v ∈ scope, hasBoundVarList v xs = false
  | _, [], _, _, _ => rfl
  | _, x :: xs, ⟨_, hx, hxs⟩, v, hv => by
    simp [hasBoundVarList, noLetShadow_implies_noBoundVar hx v hv,
      noLetShadowList_implies_noBoundVar hxs v hv]
termination_by _ xs _ _ _ => sizeOf xs

theorem noLetShadowArms_implies_noBoundVar :
    ∀ {scope : List String} {arms : List (Pat × Expr)},
      NoLetShadowArms scope arms → ∀ v ∈ scope, hasBoundVarArms v arms = false
  | _, [], _, _, _ => rfl
  | _, (p, b) :: rest, ⟨hp, hb, hrest⟩, v, hv => by
    simp [hasBoundVarArms,
      noLetShadow_implies_noBoundVar hb v (List.mem_append_right _ hv),
      noLetShadowArms_implies_noBoundVar hrest v hv]
    exact fun hmem => hp v hmem hv
termination_by _ arms _ _ _ => sizeOf arms

end

theorem noLetShadowArms_mem {scope : List String} {arms : List (Pat × Expr)} {p : Pat} {b : Expr}
    (h : NoLetShadowArms scope arms) (hmem : (p, b) ∈ arms) :
    (∀ v ∈ patBoundVars p, v ∉ scope) ∧ NoLetShadow (patBoundVars p ++ scope) b := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    rcases h with ⟨hp0, hb0, htl⟩
    rcases List.mem_cons.mp hmem with heq | hmemTl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨hp0, hb0⟩
    · exact ih htl hmemTl

mutual

theorem hasBoundVar_flattenLets_sub (v : String) :
    ∀ (fuel : Nat) (e : Expr),
      hasBoundVar v (flattenLets fuel e) = true → hasBoundVar v e = true
  | _, .literal _, h | _, .var _, h | _, .global _ _, h | _, .control _ _, h => by
    simp [flattenLets, hasBoundVar] at h
  | fuel, .tuple xs, h | fuel, .array xs, h | fuel, .construct _ _ _ xs, h
  | fuel, .constructAs _ _ _ xs, h | fuel, .record _ xs, h | fuel, .update _ xs, h
  | fuel, .builtin _ xs, h | fuel, .call _ _ xs, h => by
    simp only [flattenLets, hasBoundVar] at h ⊢
    exact hasBoundVarList_flattenLets_sub v fuel xs h
  | fuel, .repeat x _, h | fuel, .index x _, h | fuel, .slice x _ _, h
  | fuel, .member x _, h | fuel, .project x _, h | fuel, .store x, h
  | fuel, .load x, h | fuel, .hint _ x _, h | fuel, .neg x, h => by
    simp only [flattenLets, hasBoundVar] at h ⊢
    exact hasBoundVar_flattenLets_sub v fuel x h
  | fuel, .binary _ l r, h => by
    simp only [flattenLets, hasBoundVar, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_flattenLets_sub v fuel l h1)
    · exact Or.inr (hasBoundVar_flattenLets_sub v fuel r h2)
  | fuel, .matchValue s arms, h => by
    simp only [flattenLets, hasBoundVar, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_flattenLets_sub v fuel s h1)
    · exact Or.inr (hasBoundVarArms_flattenLets_sub v fuel arms h2)
  | fuel, .letValue p x body, h => by
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      cases fuel with
      | zero =>
        rw [flattenLets] at h
        simp only [hasBoundVar, Bool.or_eq_true] at h ⊢
        rcases h with (h1 | h2) | h3
        · exact Or.inl (Or.inl h1)
        · have h2' := hasBoundVar_flattenLets_sub v 0 (.letValue p1 rhs1 body1) h2
          simp only [hasBoundVar, Bool.or_eq_true] at h2'
          exact Or.inl (Or.inr h2')
        · exact Or.inr (hasBoundVar_flattenLets_sub v 0 body h3)
      | succ fuel' =>
        rw [flattenLets] at h
        split at h
        · have h' := hasBoundVar_flattenLets_sub v fuel' _ h
          simp only [hasBoundVar, Bool.or_eq_true] at h' ⊢
          rcases h' with (h1 | h2) | ((h3 | h4) | h5)
          · exact Or.inl (Or.inr (Or.inl (Or.inl h1)))
          · exact Or.inl (Or.inr (Or.inl (Or.inr h2)))
          · exact Or.inl (Or.inl h3)
          · exact Or.inl (Or.inr (Or.inr h4))
          · exact Or.inr h5
        · simp only [hasBoundVar, Bool.or_eq_true] at h ⊢
          rcases h with (h1 | h2) | h3
          · exact Or.inl (Or.inl h1)
          · have h2' := hasBoundVar_flattenLets_sub v (fuel' + 1) (.letValue p1 rhs1 body1) h2
            simp only [hasBoundVar, Bool.or_eq_true] at h2'
            exact Or.inl (Or.inr h2')
          · exact Or.inr (hasBoundVar_flattenLets_sub v (fuel' + 1) body h3)
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun a b c he => hlet ⟨a, b, c, he⟩
      rw [flattenLets_letValue_other fuel p x body hnot] at h
      simp only [hasBoundVar, Bool.or_eq_true] at h ⊢
      rcases h with (h1 | h2) | h3
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (hasBoundVar_flattenLets_sub v fuel x h2))
      · exact Or.inr (hasBoundVar_flattenLets_sub v fuel body h3)
termination_by fuel e _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec]
  all_goals omega

theorem hasBoundVarList_flattenLets_sub (v : String) :
    ∀ (fuel : Nat) (xs : List Expr),
      hasBoundVarList v (flattenLetsList fuel xs) = true → hasBoundVarList v xs = true
  | _, [], h => by simp [flattenLetsList, hasBoundVarList] at h
  | fuel, x :: xs, h => by
    simp only [flattenLetsList, hasBoundVarList, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_flattenLets_sub v fuel x h1)
    · exact Or.inr (hasBoundVarList_flattenLets_sub v fuel xs h2)
termination_by fuel xs _ => (fuel, sizeOf xs)

theorem hasBoundVarArms_flattenLets_sub (v : String) :
    ∀ (fuel : Nat) (arms : List (Pat × Expr)),
      hasBoundVarArms v (flattenLetsArms fuel arms) = true → hasBoundVarArms v arms = true
  | _, [], h => by simp [flattenLetsArms, hasBoundVarArms] at h
  | fuel, (p, b) :: rest, h => by
    simp only [flattenLetsArms, hasBoundVarArms, Bool.or_eq_true] at h ⊢
    rcases h with (h1 | h2) | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (hasBoundVar_flattenLets_sub v fuel b h2))
    · exact Or.inr (hasBoundVarArms_flattenLets_sub v fuel rest h3)
termination_by fuel arms _ => (fuel, sizeOf arms)

end

mutual

/-- `flattenLets` preserves `NoLetShadow`! -/
theorem noLetShadow_flattenLets :
    ∀ (fuel : Nat) {scope : List String} {e : Expr},
      NoLetShadow scope e → NoLetShadow scope (flattenLets fuel e)
  | _, _, .literal _, _ | _, _, .var _, _ | _, _, .global _ _, _ | _, _, .control _ _, _ => by
    simp [flattenLets, NoLetShadow]
  | fuel, _, .tuple xs, h | fuel, _, .array xs, h | fuel, _, .construct _ _ _ xs, h
  | fuel, _, .constructAs _ _ _ xs, h | fuel, _, .record _ xs, h | fuel, _, .update _ xs, h
  | fuel, _, .builtin _ xs, h | fuel, _, .call _ _ xs, h => by
    simp only [flattenLets, NoLetShadow]; exact noLetShadow_flattenLetsList fuel h
  | fuel, _, .repeat x _, h | fuel, _, .index x _, h | fuel, _, .slice x _ _, h
  | fuel, _, .member x _, h | fuel, _, .project x _, h | fuel, _, .store x, h
  | fuel, _, .load x, h | fuel, _, .hint _ x _, h | fuel, _, .neg x, h => by
    simp only [flattenLets, NoLetShadow]; exact noLetShadow_flattenLets fuel h
  | fuel, _, .binary _ l r, ⟨hdisj, hl, hr⟩ => by
    simp only [flattenLets, NoLetShadow]
    refine ⟨fun v hv => ?_, noLetShadow_flattenLets fuel hl, noLetShadow_flattenLets fuel hr⟩
    by_contra hne
    have htr : hasBoundVar v (flattenLets fuel r) = true := by
      cases h : hasBoundVar v (flattenLets fuel r) <;> simp_all
    have h1 := hasBoundVar_flattenLets_sub v fuel l hv
    have h2 := hasBoundVar_flattenLets_sub v fuel r htr
    rw [hdisj v h1] at h2; cases h2
  | fuel, _, .matchValue s arms, ⟨hs, harms⟩ => by
    simp only [flattenLets, NoLetShadow]
    exact ⟨noLetShadow_flattenLets fuel hs, noLetShadow_flattenLetsArms fuel harms⟩
  | fuel, scope, .letValue p x body, ⟨hp, hdisj, hx, hb⟩ => by
    by_cases hlet : ∃ p1 rhs1 body1, x = .letValue p1 rhs1 body1
    · obtain ⟨p1, rhs1, body1, rfl⟩ := hlet
      cases fuel with
      | zero =>
        rw [flattenLets]
        refine ⟨hp, fun v hv => ?_, noLetShadow_flattenLets 0 hx, noLetShadow_flattenLets 0 hb⟩
        have hv' := hasBoundVar_flattenLets_sub v 0 _ hv
        obtain ⟨hnp, hnb⟩ := hdisj v hv'
        refine ⟨hnp, ?_⟩
        cases hfb : hasBoundVar v (flattenLets 0 body) with
        | false => rfl
        | true => rw [hasBoundVar_flattenLets_sub v 0 body hfb] at hnb; cases hnb
      | succ fuel' =>
        rw [flattenLets]
        split
        · rcases hx with ⟨hp1, hdisj1, hrhs1, hbody1⟩
          refine noLetShadow_flattenLets fuel' ?_
          have hdisjP1 : ∀ v ∈ patBoundVars p1, v ∉ patBoundVars p ∧ hasBoundVar v body = false :=
            fun v hv => hdisj v (by simp [hasBoundVar, hv])
          have hdisjRhs1 : ∀ v, hasBoundVar v rhs1 = true → v ∉ patBoundVars p ∧ hasBoundVar v body = false :=
            fun v hv => hdisj v (by simp [hasBoundVar, hv])
          have hdisjBody1 : ∀ v, hasBoundVar v body1 = true → v ∉ patBoundVars p ∧ hasBoundVar v body = false :=
            fun v hv => hdisj v (by simp [hasBoundVar, hv])
          refine ⟨hp1, fun v hv => ?_, hrhs1, ?_⟩
          · obtain ⟨hnp1, hnb1⟩ := hdisj1 v hv
            obtain ⟨hnp, hnb⟩ := hdisjRhs1 v hv
            exact ⟨hnp1, by simp [hasBoundVar, hnp, hnb1, hnb]⟩
          · refine ⟨fun v hvp hmem => ?_, hdisjBody1, hbody1, ?_⟩
            · rcases List.mem_append.mp hmem with h1 | h2
              · exact (hdisjP1 v h1).1 hvp
              · exact hp v hvp h2
            · refine noLetShadow_scope_imp (fun v hv => ?_) hb
              rcases List.mem_append.mp hv with hvp | hrest
              · exact Or.inl (List.mem_append_left _ hvp)
              · rcases List.mem_append.mp hrest with hvp1 | hvs
                · exact Or.inr (hdisjP1 v hvp1).2
                · exact Or.inl (List.mem_append_right _ hvs)
        · refine ⟨hp, fun v hv => ?_,
            noLetShadow_flattenLets (fuel' + 1) hx, noLetShadow_flattenLets (fuel' + 1) hb⟩
          have hv' := hasBoundVar_flattenLets_sub v (fuel' + 1) _ hv
          obtain ⟨hnp, hnb⟩ := hdisj v hv'
          refine ⟨hnp, ?_⟩
          cases hfb : hasBoundVar v (flattenLets (fuel' + 1) body) with
          | false => rfl
          | true => rw [hasBoundVar_flattenLets_sub v (fuel' + 1) body hfb] at hnb; cases hnb
    · have hnot : ∀ p1 rhs1 body1, x ≠ .letValue p1 rhs1 body1 := fun a b c he => hlet ⟨a, b, c, he⟩
      rw [flattenLets_letValue_other fuel p x body hnot]
      refine ⟨hp, fun v hv => ?_, noLetShadow_flattenLets fuel hx, noLetShadow_flattenLets fuel hb⟩
      have hv' := hasBoundVar_flattenLets_sub v fuel x hv
      obtain ⟨hnp, hnb⟩ := hdisj v hv'
      refine ⟨hnp, ?_⟩
      cases hfb : hasBoundVar v (flattenLets fuel body) with
      | false => rfl
      | true => rw [hasBoundVar_flattenLets_sub v fuel body hfb] at hnb; cases hnb
termination_by fuel _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [Aiur.Generic.Expr.letValue.sizeOf_spec]
  all_goals omega

theorem noLetShadow_flattenLetsList :
    ∀ (fuel : Nat) {scope : List String} {xs : List Expr},
      NoLetShadowList scope xs → NoLetShadowList scope (flattenLetsList fuel xs)
  | _, _, [], _ => by simp [flattenLetsList, NoLetShadowList]
  | fuel, _, x :: xs, ⟨hdisj, hx, hxs⟩ => by
    simp only [flattenLetsList, NoLetShadowList]
    refine ⟨fun v hv => ?_, noLetShadow_flattenLets fuel hx, noLetShadow_flattenLetsList fuel hxs⟩
    cases hfl : hasBoundVarList v (flattenLetsList fuel xs) with
    | false => rfl
    | true =>
      have h1 := hasBoundVar_flattenLets_sub v fuel x hv
      have h2 := hasBoundVarList_flattenLets_sub v fuel xs hfl
      rw [hdisj v h1] at h2; cases h2
termination_by fuel _ xs _ => (fuel, sizeOf xs)

theorem noLetShadow_flattenLetsArms :
    ∀ (fuel : Nat) {scope : List String} {arms : List (Pat × Expr)},
      NoLetShadowArms scope arms → NoLetShadowArms scope (flattenLetsArms fuel arms)
  | _, _, [], _ => by simp [flattenLetsArms, NoLetShadowArms]
  | fuel, _, (p, b) :: rest, ⟨hp, hb, hrest⟩ => by
    simp only [flattenLetsArms, NoLetShadowArms]
    exact ⟨hp, noLetShadow_flattenLets fuel hb, noLetShadow_flattenLetsArms fuel hrest⟩
termination_by fuel _ arms _ => (fuel, sizeOf arms)

end

section ConstEnvAndPurity

variable {F : Type} [Field F] [DecidableEq F]

/-- Soundness invariant for `Peephole.ConstEnv`: every entry `(nm, k)` in `env` is bound
in `locals` to a value `v`, and whenever `Γ` types `nm` as `u32Ty`, `isU32Val k v` holds! -/
def ConstEnvOk (env : Peephole.ConstEnv) (locals : Environment F Nat) (Γ : TyEnv) : Prop :=
  ∀ nm k, env.lookup nm = some k →
    ∃ v, locals.find? (·.1 == nm) = some (nm, v) ∧
      (Γ.lookup nm = some u32Ty → isU32Val k v)

omit [DecidableEq F] in
theorem constEnvOk_nil (locals : Environment F Nat) (Γ : TyEnv) :
    ConstEnvOk [] locals Γ := by
  intro _ _ h; cases h

omit [Field F] [DecidableEq F] in
theorem lookup_envRemove_eq {names : List String} {env : Peephole.ConstEnv} {x : String} {k : Nat}
    (h : (Peephole.envRemove names env).lookup x = some k) :
    x ∉ names ∧ env.lookup x = some k := by
  induction env with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨nm, v⟩
    simp only [Peephole.envRemove, List.filter_cons] at h
    by_cases hmem : names.contains nm
    · simp only [hmem, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hxnot, hlook⟩ := ih h
      have hne : x ≠ nm := fun heq => by
        subst heq; exact hxnot (List.contains_iff_mem.mp hmem)
      exact ⟨hxnot, by simp [List.lookup, beq_false_of_ne hne, hlook]⟩
    · simp only [hmem, Bool.not_false, ↓reduceIte, List.lookup] at h
      by_cases hxeq : x = nm
      · subst hxeq
        simp only [beq_self_eq_true, Option.some.injEq] at h
        subst h
        exact ⟨fun hm => hmem (List.contains_iff_mem.mpr hm), by simp [List.lookup]⟩
      · simp only [beq_false_of_ne hxeq] at h
        obtain ⟨hxnot, hlook⟩ := ih h
        exact ⟨hxnot, by simp [List.lookup, beq_false_of_ne hxeq, hlook]⟩

omit [DecidableEq F] in
theorem constEnvOk_envRemove {env : Peephole.ConstEnv} {locals bs : Environment F Nat}
    {Γ Δ : TyEnv} {names : List String}
    (hdomB : bs.map Prod.fst = names) (hdomD : Δ.map Prod.fst = names)
    (hok : ConstEnvOk env locals Γ) :
    ConstEnvOk (Peephole.envRemove names env) (bs ++ locals) (Δ ++ Γ) := by
  intro x k hl
  obtain ⟨hnot, hl'⟩ := lookup_envRemove_eq hl
  obtain ⟨v, hv, hu⟩ := hok x k hl'
  refine ⟨v, ?_, ?_⟩
  · rw [find?_append_of_not_mem (by rw [hdomB]; exact hnot)]; exact hv
  · rw [lookup_append_of_not_mem (by rw [hdomD]; exact hnot)]; exact hu

omit [DecidableEq F] in
theorem constEnvOk_cons_val {env : Peephole.ConstEnv} {locals : Environment F Nat}
    {Γ : TyEnv} {nm : String} {k : Nat} {val : SourceValue F} {tv : Lower.Ty}
    (hok : ConstEnvOk env locals Γ)
    (hval : tv = u32Ty → isU32Val k val) :
    ConstEnvOk ((nm, k) :: Peephole.envRemove [nm] env) ((nm, val) :: locals) ((nm, tv) :: Γ) := by
  intro x k' hl
  by_cases hx : x = nm
  · subst hx
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
    subst hl
    refine ⟨val, by simp, ?_⟩
    intro hty
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hty
    exact hval hty
  · simp only [List.lookup, beq_false_of_ne hx] at hl
    obtain ⟨_, hl'⟩ := lookup_envRemove_eq hl
    obtain ⟨v, hv, hu⟩ := hok x k' hl'
    refine ⟨v, by simp [beq_false_of_ne (Ne.symm hx), hv], ?_⟩
    simp only [List.lookup, beq_false_of_ne hx]
    exact hu

omit [DecidableEq F] in
theorem constEnvOk_cons_not_mem {env : Peephole.ConstEnv} {locals : Environment F Nat}
    {Γ : TyEnv} {nm : String} {val : SourceValue F} {tv : Lower.Ty}
    (hok : ConstEnvOk env locals Γ) (hnot : nm ∉ env.map Prod.fst) :
    ConstEnvOk env ((nm, val) :: locals) ((nm, tv) :: Γ) := by
  have lookupMem : ∀ {l : Peephole.ConstEnv} {x : String} {k : Nat},
      l.lookup x = some k → x ∈ l.map Prod.fst := by
    intro l x k hl
    induction l with
    | nil => cases hl
    | cons hd tl ih =>
      rcases hd with ⟨a, b⟩
      simp only [List.lookup] at hl
      by_cases hxa : x = a
      · subst hxa; simp
      · simp only [beq_false_of_ne hxa] at hl
        exact List.mem_cons_of_mem _ (ih hl)
  intro x k hl
  have hne : x ≠ nm := fun heq => hnot (heq ▸ lookupMem hl)
  obtain ⟨v, hv, hu⟩ := hok x k hl
  refine ⟨v, by simp [beq_false_of_ne (Ne.symm hne), hv], ?_⟩
  simp only [List.lookup, beq_false_of_ne hne]
  exact hu

omit [Field F] [DecidableEq F] in
theorem envRemove_subset {names : List String} {env : Peephole.ConstEnv} {x : String}
    (hx : x ∈ (Peephole.envRemove names env).map Prod.fst) :
    x ∈ env.map Prod.fst := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩

mutual

/-- **Soundness of `Peephole.isHeapPure`**: any well-typed expression with `isHeapPure e = true`
leaves the heap unchanged! -/
theorem evalExpr_isHeapPure {world : World F} {enums : List Aiur.Generic.EnumDecl} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {e : Expr} {t : Lower.Ty}
      {h h' : Heap F} {r : SourceValue F},
      Peephole.isHeapPure e = true →
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t →
      EnvOk enums h h.length Γ locals →
      EvalExpr world [] locals (qualifyExprF F e) h r h' →
      h' = h
  | _, _, .literal _, _, _, _, _, _, _, _, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev; cases ev; rfl
  | _, _, .var _, _, _, _, _, _, _, _, ev => by
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev; cases ev; rfl
  | _, _, .tuple xs, _, _, _, _, hp, hty, henv, ev => by
    cases hty with | tuple items =>
    simp only [Peephole.isHeapPure] at hp
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    rw [map_qualifyExprF] at ev
    cases ev with | tuple evs =>
    exact evalArgs_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp items henv evs
  | _, _, .array xs, _, _, _, _, hp, hty, henv, ev => by
    cases hty with | array _ items =>
    simp only [Peephole.isHeapPure] at hp
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    rw [map_qualifyExprF] at ev
    cases ev with | array evs =>
    exact evalArgs_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp items henv evs
  | _, _, .index x _, _, _, _, _, hp, hty, henv, ev => by
    cases hty with | index hx =>
    simp only [Peephole.isHeapPure] at hp
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with | index evX _ =>
    exact evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp hx henv evX
  | _, _, .project x _, _, _, _, _, hp, hty, henv, ev => by
    cases hty with | project hx _ =>
    simp only [Peephole.isHeapPure] at hp
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with | project evX _ =>
    exact evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp hx henv evX
  | _, _, .neg x, _, _, _, _, hp, hty, henv, ev => by
    cases hty with | neg hx =>
    simp only [Peephole.isHeapPure] at hp
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with | neg evX _ =>
    exact evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp hx henv evX
  | _, _, .binary _ l r, _, _, _, _, hp, hty, henv, ev => by
    simp only [Peephole.isHeapPure, Bool.and_eq_true] at hp
    cases hty with | binary hl hr =>
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    cases ev with | binary evL evR _ =>
    have h1 := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp.1 hl henv evL
    subst h1
    exact evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp.2 hr henv evR
  | _, _, .call nm targs xs, _, _, _, _, hp, hty, henv, ev => by
    cases targs with
    | none => simp [Peephole.isHeapPure] at hp
    | some ts =>
      cases ts with
      | cons _ _ => simp [Peephole.isHeapPure] at hp
      | nil =>
        simp only [Peephole.isHeapPure, Bool.and_eq_true] at hp
        obtain ⟨hcal, hpxs⟩ := hp
        cases hty with | call hsig items =>
        rw [qualifyExprF_call] at ev
        cases ev with | call evArgs hfn =>
        have h1 := evalArgs_isHeapPure hnd hHas hProv hLib spec hWT hSigs hpxs items henv evArgs
        subst h1
        have hvals := evalArgs_valOk_ext hnd hHas hProv hLib spec hWT items henv evArgs
        have hinst : instanceName [] (qualifyName nm) (Option.map (List.map qualifyTy) (some [])) =
            qualifyName nm := by simp [instanceName, Instance.symbol]
        rw [hinst] at hfn
        simp only [Peephole.isPureU32Callee, Bool.or_eq_true, beq_iff_eq] at hcal
        rcases hcal with (((((((((((((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
        · -- UInt32::add
          rw [show qualifyName "UInt32::add" = "UInt32::add" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.add _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::add3
          rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _ | _⟩⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          obtain ⟨_, hc'⟩ := (ValOk_u32 ..).mp hc
          exact (spec.peep.add3 _ _ _ _ _ _ _ _ _ ha' hb' hc' hfn).2
        · -- UInt32::sub
          rw [show qualifyName "UInt32::sub" = "UInt32::sub" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.sub _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::xor
          rw [show qualifyName "UInt32::xor" = "UInt32::xor" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.xor _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::and
          rw [show qualifyName "UInt32::and" = "UInt32::and" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.and _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::or
          rw [show qualifyName "UInt32::or" = "UInt32::or" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.or _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::rotr8
          rw [show qualifyName "UInt32::rotr8" = "UInt32::rotr8" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | _⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha
          exact (spec.peep.rotr8 _ _ _ _ _ ha' hfn).2
        · -- UInt32::rotr16
          rw [show qualifyName "UInt32::rotr16" = "UInt32::rotr16" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | _⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha
          exact (spec.peep.rotr16 _ _ _ _ _ ha' hfn).2
        · -- UInt32::xor_rotr7
          rw [show qualifyName "UInt32::xor_rotr7" = "UInt32::xor_rotr7" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.xor_rotr7 _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::xor_rotr12
          rw [show qualifyName "UInt32::xor_rotr12" = "UInt32::xor_rotr12" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.xor_rotr12 _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- UInt32::from_bytes
          rw [show qualifyName "UInt32::from_bytes" = "UInt32::from_bytes" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | _⟩
          obtain ⟨_, ha'⟩ := (ValOk_u8Array4 ..).mp ha
          exact (spec.peep.from_bytes _ _ _ _ _ ha' hfn).2
        · -- UInt32::to_bytes
          rw [show qualifyName "UInt32::to_bytes" = "UInt32::to_bytes" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | _⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha
          exact (spec.peep.to_bytes _ _ _ _ _ ha' hfn).2
        · -- UInt32::from_field
          rw [show qualifyName "UInt32::from_field" = "UInt32::from_field" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨_, _ | _⟩
          obtain ⟨_, _, _, _, hr⟩ := spec.tg.from_field _ _ _ _ hfn
          exact hr
        · -- UInt32::from_fields
          rw [show qualifyName "UInt32::from_fields" = "UInt32::from_fields" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨_, _ | _⟩
          exact (spec.from_fields_any _ _ _ _ hfn).2
        · -- UInt32::compact
          rw [show qualifyName "UInt32::compact" = "UInt32::compact" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨ha, _ | _⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha
          exact (spec.tg.compact _ _ _ _ _ ha' hfn).2
        · -- UInt8::from_fields
          rw [show qualifyName "UInt8::from_fields" = "UInt8::from_fields" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
          exact (spec.peep.u8_from_fields _ _ _ _ _ hfn).1
        · -- UInt8::to_field
          rw [show qualifyName "UInt8::to_field" = "UInt8::to_field" from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
          simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨_, _ | _⟩
          exact (spec.tg.u8_to_field _ _ _ _ hfn).2
        · -- u32_of_field
          rw [show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl, sigsWithU32OfField_u32_of_field] at hsig
          simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨_, _ | _⟩
          exact (spec.u32_of_field _ _ _ _ hfn).2
        · -- Prog::u32_of_field
          rw [show qualifyName "Prog::u32_of_field" = qualified "u32_of_field" from rfl, sigsWithU32OfField_u32_of_field] at hsig
          simp only [Option.some.injEq, Prod.mk.injEq] at hsig; obtain ⟨rfl, rfl⟩ := hsig
          rcases hvals with _ | ⟨_, _ | _⟩
          exact (spec.u32_of_field _ _ _ _ hfn).2
        · -- u32_shr
          rw [show qualifyName "u32_shr" = qualified "u32_shr" from rfl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨rfl, rfl⟩ := hSigs.2.1 _ _ hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.shr _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- Prog::u32_shr
          rw [show qualifyName "Prog::u32_shr" = qualified "u32_shr" from rfl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨rfl, rfl⟩ := hSigs.2.1 _ _ hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.shr _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- u32_shl
          rw [show qualifyName "u32_shl" = qualified "u32_shl" from rfl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨rfl, rfl⟩ := hSigs.2.2.1 _ _ hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.shl _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- Prog::u32_shl
          rw [show qualifyName "Prog::u32_shl" = qualified "u32_shl" from rfl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨rfl, rfl⟩ := hSigs.2.2.1 _ _ hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.peep.shl _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- u32_mul
          rw [show qualifyName "u32_mul" = qualified "u32_mul" from rfl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨rfl, rfl⟩ := hSigs.2.2.2 _ _ hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.u32_mul _ _ _ _ _ _ _ ha' hb' hfn).2
        · -- Prog::u32_mul
          rw [show qualifyName "Prog::u32_mul" = qualified "u32_mul" from rfl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨rfl, rfl⟩ := hSigs.2.2.2 _ _ hsig
          rcases hvals with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
          obtain ⟨_, ha'⟩ := (ValOk_u32 ..).mp ha; obtain ⟨_, hb'⟩ := (ValOk_u32 ..).mp hb
          exact (spec.u32_mul _ _ _ _ _ _ _ ha' hb' hfn).2
  | _, _, .global .., _, _, _, _, hp, _, _, _ | _, _, .repeat .., _, _, _, _, hp, _, _, _
  | _, _, .slice .., _, _, _, _, hp, _, _, _ | _, _, .construct .., _, _, _, _, hp, _, _, _
  | _, _, .constructAs .., _, _, _, _, hp, _, _, _ | _, _, .record .., _, _, _, _, hp, _, _, _
  | _, _, .member .., _, _, _, _, hp, _, _, _ | _, _, .update .., _, _, _, _, hp, _, _, _
  | _, _, .builtin .., _, _, _, _, hp, _, _, _ | _, _, .store .., _, _, _, _, hp, _, _, _
  | _, _, .load .., _, _, _, _, hp, _, _, _ | _, _, .hint .., _, _, _, _, hp, _, _, _
  | _, _, .letValue .., _, _, _, _, hp, _, _, _ | _, _, .matchValue .., _, _, _, _, hp, _, _, _
  | _, _, .control .., _, _, _, _, hp, _, _, _ => by simp [Peephole.isHeapPure] at hp
termination_by _ _ e _ _ _ _ _ _ _ _ => sizeOf e

theorem evalArgs_isHeapPure {world : World F} {enums : List Aiur.Generic.EnumDecl} {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {xs : List Expr} {ts : List Lower.Ty}
      {h h' : Heap F} {vs : List (SourceValue F)},
      Peephole.isHeapPureList xs = true →
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      EnvOk enums h h.length Γ locals →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h' →
      h' = h
  | _, _, [], _, _, _, _, _, _, _, ev => by cases ev; rfl
  | _, _, x :: xs, _, _, _, _, hp, hty, henv, ev => by
    simp only [Peephole.isHeapPureList, Bool.and_eq_true] at hp
    cases hty with | cons hd tl =>
    cases ev with | cons evH evT =>
    have h1 := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp.1 hd henv evH
    subst h1
    exact evalArgs_isHeapPure hnd hHas hProv hLib spec hWT hSigs hp.2 tl henv evT
termination_by _ _ xs _ _ _ _ _ _ _ _ => sizeOf xs

end

/-- Any pure `UInt32` atom (`isPureU32Atom e = true`) leaves the heap unchanged and can be
re-evaluated at any other heap `h2` yielding the exact same value! -/
theorem evalExpr_isPureU32Atom_heapIndep {world : World F} (spec : U32WorldSpec world)
    {locals : Environment F Nat} {e : Expr} {h h' h2 : Heap F} {r : SourceValue F}
    (hatom : Peephole.isPureU32Atom e = true)
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    h' = h ∧ EvalExpr world [] locals (qualifyExprF F e) h2 r h2 := by
  unfold Peephole.isPureU32Atom at hatom
  split at hatom
  · simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | var hl => exact ⟨rfl, .var hl⟩
  · simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev; exact ⟨rfl, .literal⟩
  · next nm n =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hatom
    rw [qualifyExprF_call] at ev ⊢
    simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_literal] at ev ⊢
    obtain ⟨v0, hm, evL, hfn⟩ := evalExpr_call1_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL
    have hinst : instanceName [] (qualifyName nm) (some []) = qualifyName nm := by
      simp [instanceName, Instance.symbol]
    rcases hatom with (rfl | rfl) | rfl
    · obtain ⟨⟨k, hk, hfeq, hr⟩, rfl⟩ := spec.u32_of_field _ _ _ _ hfn
      refine ⟨rfl, .call (.cons .literal .nil) ?_⟩
      rw [hinst, show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl, hfeq]
      exact spec.u32_of_field_mk k r h2 hk hr
    · obtain ⟨⟨k, hk, hfeq, hr⟩, rfl⟩ := spec.u32_of_field _ _ _ _ hfn
      refine ⟨rfl, .call (.cons .literal .nil) ?_⟩
      rw [hinst, show qualifyName "Prog::u32_of_field" = qualified "u32_of_field" from rfl, hfeq]
      exact spec.u32_of_field_mk k r h2 hk hr
    · obtain ⟨k, _, hfeq, hr, rfl⟩ := spec.tg.from_field _ _ _ _ hfn
      refine ⟨rfl, .call (.cons .literal .nil) ?_⟩
      rw [hinst, show qualifyName "UInt32::from_field" = "UInt32::from_field" from rfl, hfeq]
      exact spec.from_field_mk k r h2 hr
  · cases hatom

omit [Field F] [DecidableEq F] in
private theorem extractU32Const?_inv {env : Peephole.ConstEnv} {e : Expr} {k : Nat}
    (h : Peephole.extractU32Const? env e = some k) :
    (∃ n, e = .literal n ∧ k = n % U32.base) ∨
    (∃ nm, e = .var nm ∧ env.lookup nm = some k) ∨
    (∃ nm n, e = .call nm (some []) [.literal n] ∧ Peephole.isU32OfFieldName nm = true ∧ k = n % U32.base) ∨
    (∃ b0 b1 b2 b3, e = .call "UInt32::from_fields" (some [])
      [.array [.literal b0, .literal b1, .literal b2, .literal b3]] ∧
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧ k = U32.pack b0 b1 b2 b3) ∨
    (∃ a b va vb, e = .call "UInt32::sub" (some []) [a, b] ∧
      Peephole.extractU32Const? env a = some va ∧
      Peephole.extractU32Const? env b = some vb ∧
      k = (U32.base + va - vb) % U32.base) := by
  unfold Peephole.extractU32Const? at h
  split at h
  · simp only [Option.some.injEq] at h; exact Or.inl ⟨_, rfl, h.symm⟩
  · exact Or.inr (Or.inl ⟨_, rfl, h⟩)
  · split at h
    · next his => simp only [Option.some.injEq] at h; exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, his, h.symm⟩))
    · cases h
  · split at h
    · next hlt =>
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl,
        hlt.1.1.1, hlt.1.1.2, hlt.1.2, hlt.2, h.symm⟩)))
    · cases h
  · next a b =>
    cases ha : Peephole.extractU32Const? env a with
    | none => simp [ha] at h
    | some va =>
      cases hb : Peephole.extractU32Const? env b with
      | none => simp [ha, hb] at h
      | some vb =>
        rw [ha, hb] at h; simp only [Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, va, vb, rfl, ha, hb, h.symm⟩)))
  · cases h

/-- Soundness of `Peephole.extractU32Const?` on any `u32Ty`-typed expression that evaluates. -/
theorem evalExpr_extractU32Const?_sound {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world) {env : Peephole.ConstEnv}
    {Γ : TyEnv} {locals : Environment F Nat}
    {e : Expr} {k : Nat} {h h' : Heap F} {v : SourceValue F}
    (hex : Peephole.extractU32Const? env e = some k)
    (hlb : literalsBounded e = true)
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e u32Ty)
    (hce : ConstEnvOk env locals Γ)
    (ev : EvalExpr world [] locals (qualifyExprF F e) h v h') :
    isU32Val k v ∧ h' = h := by
  rcases extractU32Const?_inv hex with
    ⟨n, rfl, rfl⟩ |
    ⟨nm, rfl, hlook⟩ |
    ⟨nm, n, rfl, his, rfl⟩ |
    ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, rfl⟩ |
    ⟨a, b, va, vb, rfl, ha, hb, rfl⟩
  · cases hty
  · cases hty with | var hl =>
    obtain ⟨v0, hfound, hu⟩ := hce nm k hlook
    rw [qualifyExprF_var] at ev
    obtain ⟨hfound', rfl⟩ := evalExpr_var_inv ev
    rw [hfound, Option.some.injEq, Prod.mk.injEq] at hfound'
    obtain ⟨_, rfl⟩ := hfound'
    exact ⟨hu hl, rfl⟩
  · rw [qualifyExprF_call] at ev
    simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_literal] at ev
    obtain ⟨v0, hm, evL, hfn⟩ := evalExpr_call1_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL
    simp only [Peephole.isU32OfFieldName, Bool.or_eq_true, beq_iff_eq] at his
    rcases his with (rfl | rfl) | rfl
    · simp only [literalsBounded, allLitsLt, beq_self_eq_true, Bool.true_or, ↓reduceIte,
        Bool.and_true, decide_eq_true_eq] at hlb
      obtain ⟨⟨k', hk', hfeq, hr⟩, rfl⟩ := spec.u32_of_field _ _ _ _ hfn
      have heq : n = k' := spec.fc.natCast_inj56 hlb hk' (Value.field.inj hfeq)
      subst heq; exact ⟨hr, rfl⟩
    · simp only [literalsBounded, allLitsLt, beq_self_eq_true, Bool.or_true, ↓reduceIte,
        Bool.and_true, decide_eq_true_eq] at hlb
      obtain ⟨⟨k', hk', hfeq, hr⟩, rfl⟩ := spec.u32_of_field _ _ _ _ hfn
      have heq : n = k' := spec.fc.natCast_inj56 hlb hk' (Value.field.inj hfeq)
      subst heq; exact ⟨hr, rfl⟩
    · simp [literalsBounded, allLitsLt] at hlb
      obtain ⟨k', hk', hfeq, hr, rfl⟩ := spec.tg.from_field _ _ _ _ hfn
      have heq : n = k' := spec.fc.natCast_inj56
        (lt_trans hlb (by decide)) (lt_trans hk' (by decide)) (Value.field.inj hfeq)
      subst heq
      rw [Nat.mod_eq_of_lt hlb]
      exact ⟨hr, rfl⟩
  · rw [qualifyExprF_call] at ev
    simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_array,
      qualifyExprF_literal, TypedGadgets.qualifyName_u32_from_fields] at ev
    obtain ⟨varr, hm, evArr, hfn⟩ := evalExpr_call1_inv ev
    obtain ⟨w0, w1, w2, w3, h1, h2, h3, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evArr
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e2
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e3
    obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, he0, he1, he2, he3, hr, rfl⟩ :=
      spec.tg.from_fields _ _ _ _ _ _ _ hfn
    have injByte : ∀ {a b : Nat}, a < 256 → b < 256 →
        (Value.field (a : F) : SourceValue F) = .field (b : F) → a = b := fun ha hb he =>
      spec.fc.natCast_inj56 (by unfold natLimit; omega) (by unfold natLimit; omega) (Value.field.inj he)
    rw [injByte hb0 hc0 he0, injByte hb1 hc1 he1, injByte hb2 hc2 he2, injByte hb3 hc3 he3]
    exact ⟨hr, rfl⟩
  · cases hty with | call hsig items =>
    rw [show qualifyName "UInt32::sub" = "UInt32::sub" from rfl,
        sigsWithU32OfField_nonProg fns rfl] at hsig
    simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨rfl, _⟩ := hsig
    cases items with | cons htyA items1 =>
    cases items1 with | cons htyB items2 =>
    have hlbArgs := literalsBounded_call_args hlb
    simp only [literalsBoundedList, Bool.and_eq_true] at hlbArgs
    rw [qualifyExprF_call] at ev
    simp only [Option.map_some, List.map_nil, List.map_cons,
      show qualifyName "UInt32::sub" = "UInt32::sub" from rfl] at ev
    obtain ⟨wa, wb, h1, hm, evA, evB, hfn⟩ := evalExpr_call2_inv ev
    obtain ⟨hwa, rfl⟩ := evalExpr_extractU32Const?_sound spec ha hlbArgs.1 htyA hce evA
    obtain ⟨hwb, rfl⟩ := evalExpr_extractU32Const?_sound spec hb hlbArgs.2.1 htyB hce evB
    exact spec.sub va vb wa wb _ v h' hwa hwb hfn
termination_by sizeOf e
decreasing_by
  all_goals try subst_vars
  all_goals simp only [Aiur.Generic.Expr.call.sizeOf_spec, List.cons.sizeOf_spec]
  all_goals omega

/-- Constructive evaluation builder for any expression recognized by `Peephole.extractU32Const?`! -/
theorem evalExpr_extractU32Const?_mk {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world) {env : Peephole.ConstEnv}
    {Γ : TyEnv} {locals : Environment F Nat}
    {e : Expr} {k : Nat} {t : Lower.Ty} (h : Heap F)
    (hex : Peephole.extractU32Const? env e = some k)
    (hlb : literalsBounded e = true)
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t)
    (hce : ConstEnvOk env locals Γ) :
    ∃ v, EvalExpr world [] locals (qualifyExprF F e) h v h ∧
      (t = u32Ty → isU32Val k v) := by
  rcases extractU32Const?_inv hex with
    ⟨n, rfl, rfl⟩ |
    ⟨nm, rfl, hlook⟩ |
    ⟨nm, n, rfl, his, rfl⟩ |
    ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, rfl⟩ |
    ⟨a, b, va, vb, rfl, ha, hb, rfl⟩
  · cases hty
    exact ⟨.field (n : F), by rw [qualifyExprF_literal]; exact .literal, fun hbad => by cases hbad⟩
  · cases hty with | var hl =>
    obtain ⟨v0, hfound, hu⟩ := hce nm k hlook
    exact ⟨v0, by rw [qualifyExprF_var]; exact .var hfound, fun ht => by subst ht; exact hu hl⟩
  · have hw : isU32Val (n % U32.base) (u32ValOfNat F (n % U32.base)) :=
      isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
    refine ⟨u32ValOfNat F (n % U32.base), ?_, fun _ => hw⟩
    rw [qualifyExprF_call]
    simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_literal]
    simp only [Peephole.isU32OfFieldName, Bool.or_eq_true, beq_iff_eq] at his
    rcases his with (rfl | rfl) | rfl
    · simp only [literalsBounded, allLitsLt, beq_self_eq_true, Bool.true_or, ↓reduceIte,
        Bool.and_true, decide_eq_true_eq] at hlb
      exact .call (.cons .literal .nil)
        (by simpa [instanceName, Instance.symbol] using spec.u32_of_field_mk n _ h hlb hw)
    · simp only [literalsBounded, allLitsLt, beq_self_eq_true, Bool.or_true, ↓reduceIte,
        Bool.and_true, decide_eq_true_eq] at hlb
      exact .call (.cons .literal .nil)
        (by simpa [instanceName, Instance.symbol, show qualifyName "Prog::u32_of_field" = qualified "u32_of_field" from rfl] using
          spec.u32_of_field_mk n _ h hlb hw)
    · simp [literalsBounded, allLitsLt] at hlb
      have hw' : isU32Val n (u32ValOfNat F (n % U32.base)) := by
        rw [Nat.mod_eq_of_lt hlb]; exact isU32Val_u32ValOfNat hlb
      exact .call (.cons .literal .nil)
        (by simpa [instanceName, Instance.symbol] using spec.from_field_mk n _ h hw')
  · let w : SourceValue F := .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]
    have hw : isU32Val (U32.pack b0 b1 b2 b3) w := ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩
    refine ⟨w, ?_, fun _ => hw⟩
    rw [qualifyExprF_call]
    simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_array,
      qualifyExprF_literal, TypedGadgets.qualifyName_u32_from_fields]
    exact .call (.cons (.array (.cons .literal (.cons .literal (.cons .literal (.cons .literal .nil))))) .nil)
      (by simpa [instanceName, Instance.symbol] using spec.from_fields_mk _ w h hw)
  · cases hty with | call hsig items =>
    rw [show qualifyName "UInt32::sub" = "UInt32::sub" from rfl,
        sigsWithU32OfField_nonProg fns rfl] at hsig
    simp only [libFnSig, Option.some.injEq, Prod.mk.injEq] at hsig
    obtain ⟨rfl, rfl⟩ := hsig
    cases items with | cons htyA items1 =>
    cases items1 with | cons htyB items2 =>
    have hlbArgs := literalsBounded_call_args hlb
    simp only [literalsBoundedList, Bool.and_eq_true] at hlbArgs
    obtain ⟨wa, evA, hwa⟩ := evalExpr_extractU32Const?_mk spec h ha hlbArgs.1 htyA hce
    obtain ⟨wb, evB, hwb⟩ := evalExpr_extractU32Const?_mk spec h hb hlbArgs.2.1 htyB hce
    let wr := u32ValOfNat F ((U32.base + va - vb) % U32.base)
    have hwr : isU32Val ((U32.base + va - vb) % U32.base) wr :=
      isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
    refine ⟨wr, ?_, fun _ => hwr⟩
    rw [qualifyExprF_call]
    simp only [Option.map_some, List.map_nil, List.map_cons,
      show qualifyName "UInt32::sub" = "UInt32::sub" from rfl]
    exact .call (.cons evA (.cons evB .nil))
      (by simpa [instanceName, Instance.symbol] using
        spec.sub_mk va vb wa wb wr h (hwa rfl) (hwb rfl) hwr)
termination_by sizeOf e
decreasing_by
  all_goals try subst_vars
  all_goals simp only [Aiur.Generic.Expr.call.sizeOf_spec, List.cons.sizeOf_spec]
  all_goals omega

end ConstEnvAndPurity

/-! ### Part 6B: Phase 2 (`Peephole.lowerByteShifts`) Typing, `literalsBounded`, & Backward Soundness -/

theorem hasTy_byteShuffleE {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {x : Expr} {slots : List (Option Nat)}
    (hlen : slots.length = 4)
    (hx : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ x u32Ty) :
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (Peephole.byteShuffleE x slots) u32Ty := by
  unfold Peephole.byteShuffleE Lower.letE Lower.callE Lower.litE Lower.vE
  refine .letValue (tx := .array u8Ty 4) (Δ := [("__peep_b", .array u8Ty 4)])
    (.call (ptys := [u32Ty]) (rty := .array u8Ty 4) ?_ (.cons hx .nil)) .bind ?_
  · rw [TypedGadgets.qualifyName_u32_to_bytes, sigsWithU32OfField_nonProg fns rfl]; rfl
  refine .letValue (tx := .tuple [u8Ty, u8Ty]) (Δ := [("__peep_z", u8Ty)])
    (.call (ptys := [.field, .field]) (rty := .tuple [u8Ty, u8Ty]) ?_ (.cons .literal (.cons .literal .nil)))
    (.tuple (.cons (.bind (t := u8Ty)) (.cons (.wildcard (t := u8Ty)) .nil))) ?_
  · rw [TypedGadgets.qualifyName_u8_from_fields, sigsWithU32OfField_nonProg fns rfl]; rfl
  refine .call (ptys := [.array u8Ty 4]) (rty := u32Ty) ?_ (.cons (.array (by simp [hlen]) ?_) .nil)
  · rw [show qualifyName "UInt32::from_bytes" = "UInt32::from_bytes" from rfl,
        sigsWithU32OfField_nonProg fns rfl]; rfl
  rcases slots with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | _⟩⟩⟩⟩ <;> simp at hlen
  have hslot : ∀ s : Option Nat,
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums
        ([("__peep_z", u8Ty)] ++ [("__peep_b", .array u8Ty 4)] ++ Γ)
        (match s with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z") u8Ty := by
    intro s; cases s with
    | none => exact .var (by simp)
    | some idx => exact .index (n := 4) (.var (by rfl))
  exact .cons (hslot s0) (.cons (hslot s1) (.cons (hslot s2) (.cons (hslot s3) .nil)))

theorem hasTy_tryLowerByteShift {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) {env : Peephole.ConstEnv} {Γ : TyEnv}
    {nm : String} {xs : List Expr} {e' : Expr} {t : Lower.Ty}
    (h : Peephole.tryLowerByteShift env nm (some []) xs = some e')
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (.call nm (some []) xs) t) :
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e' t := by
  unfold Peephole.tryLowerByteShift at h
  cases xs with
  | nil => cases h
  | cons x rest =>
    cases rest with
    | nil => cases h
    | cons c rest2 =>
      cases rest2 with
      | cons _ _ => cases h
      | nil =>
        cases hty with | call hsig items =>
        cases items with | cons hx items1 =>
        cases items1 with | cons hc items2 =>
        cases items2
        dsimp only at h
        split at h
        · next hshr =>
          rw [qualifyName_of_isShrName hshr, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨hpt, rfl⟩ := hSigs.2.1 _ _ hsig
          simp only [List.cons.injEq, and_true] at hpt
          obtain ⟨rfl, rfl⟩ := hpt
          cases hcext : Peephole.extractU32Const? env c with
          | none => simp [hcext] at h
          | some k =>
            rw [hcext] at h; simp only [Option.bind_some, Peephole.byteShrE] at h
            split at h
            · simp only [Option.some.injEq] at h; subst h; exact hx
            · simp only [Option.some.injEq] at h; subst h; exact hasTy_byteShuffleE rfl hx
            · simp only [Option.some.injEq] at h; subst h; exact hasTy_byteShuffleE rfl hx
            · simp only [Option.some.injEq] at h; subst h; exact hasTy_byteShuffleE rfl hx
            · cases h
        · split at h
          · next hshl =>
            rw [qualifyName_of_isShlName hshl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
            obtain ⟨hpt, rfl⟩ := hSigs.2.2.1 _ _ hsig
            simp only [List.cons.injEq, and_true] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            cases hcext : Peephole.extractU32Const? env c with
            | none => simp [hcext] at h
            | some k =>
              rw [hcext] at h; simp only [Option.bind_some, Peephole.byteShlE] at h
              split at h
              · simp only [Option.some.injEq] at h; subst h; exact hx
              · simp only [Option.some.injEq] at h; subst h; exact hasTy_byteShuffleE rfl hx
              · simp only [Option.some.injEq] at h; subst h; exact hasTy_byteShuffleE rfl hx
              · simp only [Option.some.injEq] at h; subst h; exact hasTy_byteShuffleE rfl hx
              · cases h
          · cases h

theorem lowerByteShiftsList_length (env : Peephole.ConstEnv) :
    ∀ xs : List Expr, (Peephole.lowerByteShiftsList env xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (lowerByteShiftsList_length env xs)

mutual

theorem hasTy_lowerByteShifts {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t →
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (Peephole.lowerByteShifts env e) t
  | _, _, _, _, .literal => .literal
  | _, _, _, _, .var hl => .var hl
  | env, _, _, _, .tuple items => .tuple (hasTy_lowerByteShiftsList hSigs env items)
  | env, _, _, _, .array hlen items =>
    .array (by rw [lowerByteShiftsList_length]; exact hlen) (hasTy_lowerByteShiftsList hSigs env items)
  | env, _, _, _, .repeat hx => .repeat (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .index hx => .index (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .project hx hget => .project (hasTy_lowerByteShifts hSigs env hx) hget
  | env, _, _, _, .slice hnot hx => .slice hnot (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .construct h1 h2 h3 h4 hctor items =>
    .construct h1 h2 h3 h4 hctor (hasTy_lowerByteShiftsList hSigs env items)
  | env, _, _, _, .builtin items => .builtin (hasTy_lowerByteShiftsList hSigs env items)
  | env, _, _, _, .store hx => .store (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .load hx => .load (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .hint hfo hx => .hint hfo (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .neg hx => .neg (hasTy_lowerByteShifts hSigs env hx)
  | env, _, _, _, .binary hl hr =>
    .binary (hasTy_lowerByteShifts hSigs env hl) (hasTy_lowerByteShifts hSigs env hr)
  | env, _, _, _, .call (nm := nm) hsig items => by
    simp only [Peephole.lowerByteShifts]
    have hcall : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums _
        (.call nm (some []) (Peephole.lowerByteShiftsList env _)) _ :=
      .call hsig (hasTy_lowerByteShiftsList hSigs env items)
    cases htr : Peephole.tryLowerByteShift env nm (some []) (Peephole.lowerByteShiftsList env _) with
    | none => simpa using hcall
    | some e' => simpa using hasTy_tryLowerByteShift hSigs htr hcall
  | env, _, _, _, .letValue (p := p) hx hp hb => by
    cases p with
    | bind nm =>
      simp only [Peephole.lowerByteShifts]
      exact .letValue (hasTy_lowerByteShifts hSigs env hx) hp (hasTy_lowerByteShifts hSigs _ hb)
    | literal _ | wildcard | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.lowerByteShifts]
      exact .letValue (hasTy_lowerByteShifts hSigs env hx) hp (hasTy_lowerByteShifts hSigs _ hb)
  | env, _, _, _, .matchValue hs harms =>
    .matchValue (hasTy_lowerByteShifts hSigs env hs) (hasTy_lowerByteShiftsArms hSigs env harms)

theorem hasTy_lowerByteShiftsList {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ (Peephole.lowerByteShiftsList env xs) ts
  | _, _, _, _, .nil => .nil
  | env, _, _, _, .cons hd tl =>
    .cons (hasTy_lowerByteShifts hSigs env hd) (hasTy_lowerByteShiftsList hSigs env tl)

theorem hasTy_lowerByteShiftsArms {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms (sigsWithU32OfField (fnSigsOf fns)) enums Γ ts arms tb →
      HasTyArms (sigsWithU32OfField (fnSigsOf fns)) enums Γ ts (Peephole.lowerByteShiftsArms env arms) tb
  | _, _, _, _, _, .nil => .nil
  | env, _, _, _, _, .cons hp hb tl =>
    .cons hp (hasTy_lowerByteShifts hSigs _ hb) (hasTy_lowerByteShiftsArms hSigs env tl)

end

theorem literalsBounded_byteShuffleE {x : Expr} {slots : List (Option Nat)}
    (hx : literalsBounded x = true) :
    literalsBounded (Peephole.byteShuffleE x slots) = true := by
  have hslots : ∀ l : List (Option Nat),
      literalsBoundedList (l.map fun
        | some idx => .index (.var "__peep_b") idx
        | none => .var "__peep_z") = true := by
    intro l; induction l with
    | nil => rfl
    | cons o tl ih => cases o <;> simp [literalsBoundedList, literalsBounded, ih]
  unfold Peephole.byteShuffleE Lower.letE Lower.callE Lower.litE Lower.vE
  simp [literalsBounded, literalsBoundedList, hx]
  exact hslots slots

theorem allLitsLt_byteShuffleE {bound : Nat} (hb : 0 < bound) {x : Expr} {slots : List (Option Nat)}
    (hx : allLitsLt bound x = true) :
    allLitsLt bound (Peephole.byteShuffleE x slots) = true := by
  have hslots : ∀ l : List (Option Nat),
      allLitsLtList bound (l.map fun
        | some idx => .index (.var "__peep_b") idx
        | none => .var "__peep_z") = true := by
    intro l; induction l with
    | nil => rfl
    | cons o tl ih => cases o <;> simp [allLitsLtList, allLitsLt, ih]
  unfold Peephole.byteShuffleE Lower.letE Lower.callE Lower.litE Lower.vE
  simp [allLitsLt, allLitsLtList, hx, hb]
  exact hslots slots

mutual

theorem allLitsLt_lowerByteShifts {bound : Nat} (hb : 0 < bound) :
    ∀ (env : Peephole.ConstEnv) {e : Expr},
      allLitsLt bound e = true → allLitsLt bound (Peephole.lowerByteShifts env e) = true
  | _, .literal _, h => h
  | _, .var _, _ | _, .global _ _, _ => rfl
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h | env, .control _ x, h =>
    allLitsLt_lowerByteShifts hb env (e := x) h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => allLitsLt_lowerByteShiftsList hb env h
  | env, .binary _ l r, h => by
    simp only [Peephole.lowerByteShifts, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_lowerByteShifts hb env h.1, allLitsLt_lowerByteShifts hb env h.2⟩
  | env, .letValue p v b, h => by
    simp only [allLitsLt, Bool.and_eq_true] at h
    cases p <;> simp only [Peephole.lowerByteShifts, allLitsLt, Bool.and_eq_true] <;>
      exact ⟨allLitsLt_lowerByteShifts hb env h.1, allLitsLt_lowerByteShifts hb _ h.2⟩
  | env, .matchValue s arms, h => by
    simp only [Peephole.lowerByteShifts, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_lowerByteShifts hb env h.1, allLitsLt_lowerByteShiftsArms hb env h.2⟩
  | env, .call nm targs xs, h => by
    simp only [Peephole.lowerByteShifts]
    have hxs' := allLitsLt_lowerByteShiftsList hb env h
    cases htr : Peephole.tryLowerByteShift env nm targs (Peephole.lowerByteShiftsList env xs) with
    | none => simpa [allLitsLt] using hxs'
    | some e' =>
      simp only [Option.getD_some]
      unfold Peephole.tryLowerByteShift at htr
      split at htr
      · next x' c' heq =>
        rw [heq] at hxs'; simp only [allLitsLtList, Bool.and_eq_true] at hxs'
        split at htr
        · cases hc : Peephole.extractU32Const? env c' with
          | none => simp [hc] at htr
          | some k =>
            rw [hc] at htr; simp only [Option.bind_some, Peephole.byteShrE] at htr
            split at htr
            · simp only [Option.some.injEq] at htr; subst htr; exact hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact allLitsLt_byteShuffleE hb hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact allLitsLt_byteShuffleE hb hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact allLitsLt_byteShuffleE hb hxs'.1
            · cases htr
        · split at htr
          · cases hc : Peephole.extractU32Const? env c' with
            | none => simp [hc] at htr
            | some k =>
              rw [hc] at htr; simp only [Option.bind_some, Peephole.byteShlE] at htr
              split at htr
              · simp only [Option.some.injEq] at htr; subst htr; exact hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact allLitsLt_byteShuffleE hb hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact allLitsLt_byteShuffleE hb hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact allLitsLt_byteShuffleE hb hxs'.1
              · cases htr
          · cases htr
      · cases htr
termination_by _ e _ => sizeOf e

theorem allLitsLt_lowerByteShiftsList {bound : Nat} (hb : 0 < bound) :
    ∀ (env : Peephole.ConstEnv) {xs : List Expr},
      allLitsLtList bound xs = true → allLitsLtList bound (Peephole.lowerByteShiftsList env xs) = true
  | _, [], _ => rfl
  | env, x :: xs, h => by
    simp only [Peephole.lowerByteShiftsList, allLitsLtList, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_lowerByteShifts hb env h.1, allLitsLt_lowerByteShiftsList hb env h.2⟩
termination_by _ xs _ => sizeOf xs

theorem allLitsLt_lowerByteShiftsArms {bound : Nat} (hb : 0 < bound) :
    ∀ (env : Peephole.ConstEnv) {arms : List (Pat × Expr)},
      allLitsLtArms bound arms = true → allLitsLtArms bound (Peephole.lowerByteShiftsArms env arms) = true
  | _, [], _ => rfl
  | env, (p, b) :: rest, h => by
    simp only [Peephole.lowerByteShiftsArms, allLitsLtArms, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_lowerByteShifts hb _ h.1, allLitsLt_lowerByteShiftsArms hb env h.2⟩
termination_by _ arms _ => sizeOf arms

end

mutual

theorem literalsBounded_lowerByteShifts :
    ∀ (env : Peephole.ConstEnv) {e : Expr},
      literalsBounded e = true → literalsBounded (Peephole.lowerByteShifts env e) = true
  | _, .literal _, _ | _, .var _, _ | _, .global _ _, _ => rfl
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h | env, .control _ x, h =>
    literalsBounded_lowerByteShifts env (e := x) h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => literalsBounded_lowerByteShiftsList env h
  | env, .binary _ l r, h => by
    simp only [Peephole.lowerByteShifts, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_lowerByteShifts env h.1, literalsBounded_lowerByteShifts env h.2⟩
  | env, .letValue p v b, h => by
    simp only [literalsBounded, Bool.and_eq_true] at h
    cases p <;> simp only [Peephole.lowerByteShifts, literalsBounded, Bool.and_eq_true] <;>
      exact ⟨literalsBounded_lowerByteShifts env h.1, literalsBounded_lowerByteShifts _ h.2⟩
  | env, .matchValue s arms, h => by
    simp only [Peephole.lowerByteShifts, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_lowerByteShifts env h.1, literalsBounded_lowerByteShiftsArms env h.2⟩
  | env, .call nm targs xs, h => by
    simp only [Peephole.lowerByteShifts]
    have hxs' : literalsBoundedList (Peephole.lowerByteShiftsList env xs) = true :=
      literalsBounded_lowerByteShiftsList env (literalsBounded_call_args h)
    cases htr : Peephole.tryLowerByteShift env nm targs (Peephole.lowerByteShiftsList env xs) with
    | some e' =>
      simp only [Option.getD_some]
      unfold Peephole.tryLowerByteShift at htr
      split at htr
      · next x' c' heq =>
        rw [heq] at hxs'
        simp only [literalsBoundedList, Bool.and_eq_true] at hxs'
        split at htr
        · cases hc : Peephole.extractU32Const? env c' with
          | none => simp [hc] at htr
          | some k =>
            rw [hc] at htr; simp only [Option.bind_some, Peephole.byteShrE] at htr
            split at htr
            · simp only [Option.some.injEq] at htr; subst htr; exact hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact literalsBounded_byteShuffleE hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact literalsBounded_byteShuffleE hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact literalsBounded_byteShuffleE hxs'.1
            · cases htr
        · split at htr
          · cases hc : Peephole.extractU32Const? env c' with
            | none => simp [hc] at htr
            | some k =>
              rw [hc] at htr; simp only [Option.bind_some, Peephole.byteShlE] at htr
              split at htr
              · simp only [Option.some.injEq] at htr; subst htr; exact hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact literalsBounded_byteShuffleE hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact literalsBounded_byteShuffleE hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact literalsBounded_byteShuffleE hxs'.1
              · cases htr
          · cases htr
      · cases htr
    | none =>
      simp only [Option.getD_none]
      cases targs with
      | none => simpa [literalsBounded] using hxs'
      | some ts =>
        cases ts with
        | cons _ _ => simpa [literalsBounded] using hxs'
        | nil =>
          cases xs with
          | nil => rfl
          | cons x rest =>
            cases rest with
            | cons y rest2 =>
              simp only [Peephole.lowerByteShiftsList, literalsBounded, literalsBoundedList,
                Bool.and_eq_true] at hxs' ⊢
              exact hxs'
            | nil =>
              simp only [Peephole.lowerByteShiftsList, literalsBounded] at h ⊢
              cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
              | true =>
                simp only [h1, ↓reduceIte, Bool.and_eq_true] at h ⊢
                exact ⟨allLitsLt_lowerByteShifts (by unfold natLimit; omega) env h.1,
                       literalsBounded_lowerByteShifts env h.2⟩
              | false =>
                simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases h2 : (nm == "UInt32::from_field") with
                | true =>
                  simp only [h2, ↓reduceIte, Bool.and_eq_true] at h ⊢
                  exact ⟨allLitsLt_lowerByteShifts (by unfold U32.base; omega) env h.1,
                         literalsBounded_lowerByteShifts env h.2⟩
                | false =>
                  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  exact literalsBounded_lowerByteShifts env h
termination_by _ e _ => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem literalsBounded_lowerByteShiftsList :
    ∀ (env : Peephole.ConstEnv) {xs : List Expr},
      literalsBoundedList xs = true → literalsBoundedList (Peephole.lowerByteShiftsList env xs) = true
  | _, [], _ => rfl
  | env, x :: xs, h => by
    simp only [Peephole.lowerByteShiftsList, literalsBoundedList, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_lowerByteShifts env h.1, literalsBounded_lowerByteShiftsList env h.2⟩
termination_by _ xs _ => sizeOf xs

theorem literalsBounded_lowerByteShiftsArms :
    ∀ (env : Peephole.ConstEnv) {arms : List (Pat × Expr)},
      literalsBoundedArms arms = true → literalsBoundedArms (Peephole.lowerByteShiftsArms env arms) = true
  | _, [], _ => rfl
  | env, (p, b) :: rest, h => by
    simp only [Peephole.lowerByteShiftsArms, literalsBoundedArms, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_lowerByteShifts _ h.1, literalsBounded_lowerByteShiftsArms env h.2⟩
termination_by _ arms _ => sizeOf arms

end

section LowerByteShiftsEval

variable {F : Type} [Field F] [DecidableEq F]

private def pickSlotByte (b0 b1 b2 b3 : Nat) : Option Nat → Nat
  | some 0 => b0
  | some 1 => b1
  | some 2 => b2
  | some 3 => b3
  | _ => 0

/-- Invert `Peephole.byteShuffleE x [s0, s1, s2, s3]` for arbitrary (possibly heap-allocating!)
well-typed `x : u32Ty`. -/
private theorem evalExpr_byteShuffleE_inv_gen {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns)
    {Γ : TyEnv} {locals : Environment F Nat} {x : Expr}
    {s0 s1 s2 s3 : Option Nat} {h h' : Heap F} {r : SourceValue F}
    (hs0 : s0.all (· < 4) = true) (hs1 : s1.all (· < 4) = true)
    (hs2 : s2.all (· < 4) = true) (hs3 : s3.all (· < 4) = true)
    (hx : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ x u32Ty)
    (henv : EnvOk enums h h.length Γ locals)
    (ev : EvalExpr world [] locals (qualifyExprF F (Peephole.byteShuffleE x [s0, s1, s2, s3])) h r h') :
    ∃ vx b0 b1 b2 b3,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      EvalExpr world [] locals (qualifyExprF F x) h vx h' ∧
      isU32Val (U32.pack b0 b1 b2 b3) vx ∧
      isU32Val (U32.pack (pickSlotByte b0 b1 b2 b3 s0) (pickSlotByte b0 b1 b2 b3 s1)
        (pickSlotByte b0 b1 b2 b3 s2) (pickSlotByte b0 b1 b2 b3 s3)) r := by
  unfold Peephole.byteShuffleE Lower.letE Lower.callE Lower.litE Lower.vE at ev
  rw [qualifyExprF_letValue, qualifyExprF_call, qualifyExprF_letValue, qualifyExprF_call,
    qualifyExprF_call] at ev
  simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, Option.map_some, List.map_nil,
    List.map_cons, qualifyExprF_array, qualifyExprF_literal,
    TypedGadgets.qualifyName_u32_to_bytes, TypedGadgets.qualifyName_u8_from_fields,
    show qualifyName "UInt32::from_bytes" = "UInt32::from_bytes" from rfl] at ev
  obtain ⟨vb, h1, evTb, evRest1⟩ := evalExpr_let_bind_inv ev
  obtain ⟨vx, h0', evX, hfnTb⟩ := evalExpr_call1_inv evTb
  have hokX := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hx henv evX
  obtain ⟨nx, hvx⟩ := (ValOk_u32 ..).mp hokX
  obtain ⟨rfl, rfl⟩ := spec.peep.to_bytes nx vx h0' vb h1 hvx hfnTb
  obtain ⟨vz, vw, h2, evZ, evRest2⟩ := evalExpr_let_tuple2_wild_inv evRest1
  obtain ⟨v0, v1, hz1, hz2, evL0, evL1, hfnZ⟩ := evalExpr_call2_inv evZ
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL0
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL1
  obtain ⟨rfl, a0, a1, _ha0, _ha1, hfa0, _hfa1, htupZ⟩ := spec.peep.u8_from_fields _ _ _ _ _ hfnZ
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupZ
  obtain ⟨rfl, _⟩ := htupZ
  have ha0Zero : a0 = 0 := by
    have heq : ((0 : Nat) : F) = (a0 : F) := by simpa [Value.field.injEq] using hfa0
    exact (spec.fc.toU32Compatible (by unfold U32.base; change 0 < 3 * 4294967296; omega)
      (by unfold U32.base; change a0 < 3 * 4294967296; omega) heq).symm
  subst ha0Zero
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := hvx
  obtain ⟨varr, h3, evArr, hfnFb⟩ := evalExpr_call1_inv evRest2
  obtain ⟨w0, w1, w2, w3, ha1, ha2, ha3, ev0, ev1, ev2, ev3, rfl⟩ := evalExpr_array4_inv evArr
  have evalSlot : ∀ (s : Option Nat) (hf : Heap F) (w : SourceValue F) (hf' : Heap F),
      EvalExpr world []
        (("__peep_z", Value.field ((0 : Nat) : F)) ::
          ("__peep_b", Value.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]) ::
          locals)
        (qualifyExprF F (match s with | some idx => .index (.var "__peep_b") idx | none => .var "__peep_z"))
        hf w hf' →
      s.all (· < 4) = true →
      w = .field ((pickSlotByte b0 b1 b2 b3 s : Nat) : F) ∧ hf' = hf := by
    intro s hf w hf' evs hi
    cases s with
    | none =>
      rw [qualifyExprF_var] at evs
      obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evs
      simp at hlook
      exact ⟨by simpa [pickSlotByte] using hlook.symm, rfl⟩
    | some idx =>
      rw [qualifyExprF_index, qualifyExprF_var] at evs
      obtain ⟨vv, evv, hproj⟩ := evalExpr_index_inv evs
      obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evv
      simp at hlook; subst hlook
      simp only [Option.all_some, decide_eq_true_eq] at hi
      rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3) with rfl | rfl | rfl | rfl <;>
        · simp [Aiur.projectValue] at hproj
          exact ⟨by simpa [pickSlotByte] using hproj.symm, rfl⟩
  obtain ⟨rfl, rfl⟩ := evalSlot s0 _ w0 ha1 ev0 hs0
  obtain ⟨rfl, rfl⟩ := evalSlot s1 _ w1 ha2 ev1 hs1
  obtain ⟨rfl, rfl⟩ := evalSlot s2 _ w2 ha3 ev2 hs2
  obtain ⟨rfl, rfl⟩ := evalSlot s3 _ w3 h3 ev3 hs3
  have pickLt : ∀ s : Option Nat, pickSlotByte b0 b1 b2 b3 s < 256 := by
    intro s; cases s with
    | none => simp [pickSlotByte]
    | some idx => rcases idx with _ | _ | _ | _ | _ <;> simp [pickSlotByte] <;> omega
  have hU32Arr : isU32Val
      (U32.pack (pickSlotByte b0 b1 b2 b3 s0) (pickSlotByte b0 b1 b2 b3 s1)
        (pickSlotByte b0 b1 b2 b3 s2) (pickSlotByte b0 b1 b2 b3 s3))
      (.tuple [
        .field ((pickSlotByte b0 b1 b2 b3 s0 : Nat) : F),
        .field ((pickSlotByte b0 b1 b2 b3 s1 : Nat) : F),
        .field ((pickSlotByte b0 b1 b2 b3 s2 : Nat) : F),
        .field ((pickSlotByte b0 b1 b2 b3 s3 : Nat) : F)]) :=
    ⟨_, _, _, _, pickLt s0, pickLt s1, pickLt s2, pickLt s3, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := spec.peep.from_bytes _ _ _ _ _ hU32Arr hfnFb
  exact ⟨_, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX,
    ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩, hU32Arr⟩

theorem evalExpr_tryLowerByteShift_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns)
    {env : Peephole.ConstEnv} {Γ : TyEnv} {locals : Environment F Nat}
    {nm : String} {xs : List Expr} {e' : Expr} {t : Lower.Ty} {h h' : Heap F} {r : SourceValue F}
    (htr : Peephole.tryLowerByteShift env nm (some []) xs = some e')
    (hlb : literalsBounded (.call nm (some []) xs) = true)
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (.call nm (some []) xs) t)
    (henv : EnvOk enums h h.length Γ locals)
    (hce : ConstEnvOk env locals Γ)
    (ev : EvalExpr world [] locals (qualifyExprF F e') h r h') :
    EvalExpr world [] locals (qualifyExprF F (.call nm (some []) xs)) h r h' := by
  unfold Peephole.tryLowerByteShift at htr
  cases xs with
  | nil => cases htr
  | cons x rest =>
    cases rest with
    | nil => cases htr
    | cons c rest2 =>
      cases rest2 with
      | cons _ _ => cases htr
      | nil =>
        cases hty with | call hsig items =>
        cases items with | cons hx items1 =>
        cases items1 with | cons hc items2 =>
        cases items2
        have hlbArgs := literalsBounded_call_args hlb
        simp only [literalsBoundedList, Bool.and_eq_true] at hlbArgs
        dsimp only at htr
        split at htr
        · next hshr =>
          have hq := qualifyName_of_isShrName hshr
          rw [hq, sigsWithU32OfField_of_ne _ (by decide)] at hsig
          obtain ⟨hpt, rfl⟩ := hSigs.2.1 _ _ hsig
          simp only [List.cons.injEq, and_true] at hpt
          obtain ⟨rfl, rfl⟩ := hpt
          cases hcext : Peephole.extractU32Const? env c with
          | none => simp [hcext] at htr
          | some k =>
            rw [hcext] at htr; simp only [Option.bind_some, Peephole.byteShrE] at htr
            rw [qualifyExprF_call]
            simp only [Option.map_some, List.map_nil, List.map_cons, hq]
            have hinst : instanceName [] (qualified "u32_shr") (some []) = qualified "u32_shr" := by
              simp [instanceName, Instance.symbol]
            split at htr
            · next hk0 =>
              simp only [Option.some.injEq] at htr; subst htr
              have hokX := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hx henv ev
              obtain ⟨nx, hnx⟩ := (ValOk_u32 ..).mp hokX
              obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
              have hres : isU32Val (nx >>> (k % 32)) r := by rwa [hk0, Nat.shiftRight_zero]
              exact .call (.cons ev (.cons evC .nil))
                (by rw [hinst]; exact spec.shr_mk nx k r vc r h' hnx (hvc rfl) hres)
            · next hk8 =>
              simp only [Option.some.injEq] at htr; subst htr
              obtain ⟨vx, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX, hvx, hres⟩ :=
                evalExpr_byteShuffleE_inv_gen hnd hHas hProv hLib spec hWT rfl rfl rfl rfl hx henv ev
              obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
              have hpack : U32.pack b0 b1 b2 b3 >>> (k % 32) =
                  U32.pack (pickSlotByte b0 b1 b2 b3 (some 1)) (pickSlotByte b0 b1 b2 b3 (some 2))
                    (pickSlotByte b0 b1 b2 b3 (some 3)) (pickSlotByte b0 b1 b2 b3 none) := by
                rw [hk8]; exact Peephole.shr8_pack hb0 hb1 hb2 hb3
              rw [← hpack] at hres
              exact .call (.cons evX (.cons evC .nil))
                (by rw [hinst]; exact spec.shr_mk _ k vx vc r h' hvx (hvc rfl) hres)
            · next hk16 =>
              simp only [Option.some.injEq] at htr; subst htr
              obtain ⟨vx, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX, hvx, hres⟩ :=
                evalExpr_byteShuffleE_inv_gen hnd hHas hProv hLib spec hWT rfl rfl rfl rfl hx henv ev
              obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
              have hpack : U32.pack b0 b1 b2 b3 >>> (k % 32) =
                  U32.pack (pickSlotByte b0 b1 b2 b3 (some 2)) (pickSlotByte b0 b1 b2 b3 (some 3))
                    (pickSlotByte b0 b1 b2 b3 none) (pickSlotByte b0 b1 b2 b3 none) := by
                rw [hk16]; exact Peephole.shr16_pack hb0 hb1 hb2 hb3
              rw [← hpack] at hres
              exact .call (.cons evX (.cons evC .nil))
                (by rw [hinst]; exact spec.shr_mk _ k vx vc r h' hvx (hvc rfl) hres)
            · next hk24 =>
              simp only [Option.some.injEq] at htr; subst htr
              obtain ⟨vx, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX, hvx, hres⟩ :=
                evalExpr_byteShuffleE_inv_gen hnd hHas hProv hLib spec hWT rfl rfl rfl rfl hx henv ev
              obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
              have hpack : U32.pack b0 b1 b2 b3 >>> (k % 32) =
                  U32.pack (pickSlotByte b0 b1 b2 b3 (some 3)) (pickSlotByte b0 b1 b2 b3 none)
                    (pickSlotByte b0 b1 b2 b3 none) (pickSlotByte b0 b1 b2 b3 none) := by
                rw [hk24]; exact Peephole.shr24_pack hb0 hb1 hb2 hb3
              rw [← hpack] at hres
              exact .call (.cons evX (.cons evC .nil))
                (by rw [hinst]; exact spec.shr_mk _ k vx vc r h' hvx (hvc rfl) hres)
            · cases htr
        · split at htr
          · next hshl =>
            have hq := qualifyName_of_isShlName hshl
            rw [hq, sigsWithU32OfField_of_ne _ (by decide)] at hsig
            obtain ⟨hpt, rfl⟩ := hSigs.2.2.1 _ _ hsig
            simp only [List.cons.injEq, and_true] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            cases hcext : Peephole.extractU32Const? env c with
            | none => simp [hcext] at htr
            | some k =>
              rw [hcext] at htr; simp only [Option.bind_some, Peephole.byteShlE] at htr
              rw [qualifyExprF_call]
              simp only [Option.map_some, List.map_nil, List.map_cons, hq]
              have hinst : instanceName [] (qualified "u32_shl") (some []) = qualified "u32_shl" := by
                simp [instanceName, Instance.symbol]
              split at htr
              · next hk0 =>
                simp only [Option.some.injEq] at htr; subst htr
                have hokX := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hx henv ev
                obtain ⟨nx, hnx⟩ := (ValOk_u32 ..).mp hokX
                obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
                have hres : isU32Val ((nx <<< (k % 32)) % U32.base) r := by
                  rwa [hk0, Nat.shiftLeft_zero, Nat.mod_eq_of_lt (isU32Val_lt hnx)]
                exact .call (.cons ev (.cons evC .nil))
                  (by rw [hinst]; exact spec.shl_mk nx k r vc r h' hnx (hvc rfl) hres)
              · next hk8 =>
                simp only [Option.some.injEq] at htr; subst htr
                obtain ⟨vx, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX, hvx, hres⟩ :=
                  evalExpr_byteShuffleE_inv_gen hnd hHas hProv hLib spec hWT rfl rfl rfl rfl hx henv ev
                obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
                have hpack : (U32.pack b0 b1 b2 b3 <<< (k % 32)) % U32.base =
                    U32.pack (pickSlotByte b0 b1 b2 b3 none) (pickSlotByte b0 b1 b2 b3 (some 0))
                      (pickSlotByte b0 b1 b2 b3 (some 1)) (pickSlotByte b0 b1 b2 b3 (some 2)) := by
                  rw [hk8]; exact Peephole.shl8_pack hb0 hb1 hb2 hb3
                rw [← hpack] at hres
                exact .call (.cons evX (.cons evC .nil))
                  (by rw [hinst]; exact spec.shl_mk _ k vx vc r h' hvx (hvc rfl) hres)
              · next hk16 =>
                simp only [Option.some.injEq] at htr; subst htr
                obtain ⟨vx, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX, hvx, hres⟩ :=
                  evalExpr_byteShuffleE_inv_gen hnd hHas hProv hLib spec hWT rfl rfl rfl rfl hx henv ev
                obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
                have hpack : (U32.pack b0 b1 b2 b3 <<< (k % 32)) % U32.base =
                    U32.pack (pickSlotByte b0 b1 b2 b3 none) (pickSlotByte b0 b1 b2 b3 none)
                      (pickSlotByte b0 b1 b2 b3 (some 0)) (pickSlotByte b0 b1 b2 b3 (some 1)) := by
                  rw [hk16]; exact Peephole.shl16_pack hb0 hb1 hb2 hb3
                rw [← hpack] at hres
                exact .call (.cons evX (.cons evC .nil))
                  (by rw [hinst]; exact spec.shl_mk _ k vx vc r h' hvx (hvc rfl) hres)
              · next hk24 =>
                simp only [Option.some.injEq] at htr; subst htr
                obtain ⟨vx, b0, b1, b2, b3, hb0, hb1, hb2, hb3, evX, hvx, hres⟩ :=
                  evalExpr_byteShuffleE_inv_gen hnd hHas hProv hLib spec hWT rfl rfl rfl rfl hx henv ev
                obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h' hcext hlbArgs.2.1 hc hce
                have hpack : (U32.pack b0 b1 b2 b3 <<< (k % 32)) % U32.base =
                    U32.pack (pickSlotByte b0 b1 b2 b3 none) (pickSlotByte b0 b1 b2 b3 none)
                      (pickSlotByte b0 b1 b2 b3 none) (pickSlotByte b0 b1 b2 b3 (some 0)) := by
                  rw [hk24]; exact Peephole.shl24_pack hb0 hb1 hb2 hb3
                rw [← hpack] at hres
                exact .call (.cons evX (.cons evC .nil))
                  (by rw [hinst]; exact spec.shl_mk _ k vx vc r h' hvx (hvc rfl) hres)
              · cases htr
          · cases htr

private theorem lowerByteShiftsArms_eq_map (env : Peephole.ConstEnv) (arms : List (Pat × Expr)) :
    Peephole.lowerByteShiftsArms env arms =
      arms.map fun arm => (arm.1, Peephole.lowerByteShifts (Peephole.envRemove (Peephole.patBoundNames arm.1) env) arm.2) := by
  induction arms with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨p, b⟩; simp [Peephole.lowerByteShiftsArms, ih]

mutual

/-- **Phase 2 (`Peephole.lowerByteShifts`) Backward Soundness!** -/
theorem evalExpr_lowerByteShifts_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {locals : Environment F Nat}
      {e : Expr} {t : Lower.Ty} {h h' : Heap F} {r : SourceValue F},
      literalsBounded e = true →
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t →
      EnvOk enums h h.length Γ locals →
      ConstEnvOk env locals Γ →
      EvalExpr world [] locals (qualifyExprF F (Peephole.lowerByteShifts env e)) h r h' →
      EvalExpr world [] locals (qualifyExprF F e) h r h'
  | _, _, _, _, _, _, _, _, _, .literal, _, _, ev => ev
  | _, _, _, _, _, _, _, _, _, .var _, _, _, ev => ev
  | env, _, _, _, _, _, _, _, hlb, .tuple items, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple evs =>
      exact .tuple (evalArgs_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb items henv hce evs)
  | env, _, _, _, _, _, _, _, hlb, .array _ items, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array evs =>
      exact .array (evalArgs_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb items henv hce evs)
  | env, _, _, _, _, _, _, _, hlb, .repeat hx, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item =>
      exact .repeat (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item)
  | env, _, _, _, _, _, _, _, hlb, .index hx, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp =>
      exact .index (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item) hp
  | env, _, _, _, _, _, _, _, hlb, .project hx _, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp =>
      exact .project (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item) hp
  | env, _, _, _, _, _, _, _, hlb, .slice _ hx, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs =>
      exact .slice (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item) hs
  | env, _, _, _, _, _, _, _, hlb, .construct _ _ _ _ _ items, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct evs =>
      exact .construct (evalArgs_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb items henv hce evs)
  | env, _, _, _, _, _, _, _, hlb, .builtin items, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin evs ha =>
      exact .builtin (evalArgs_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb items henv hce evs) ha
  | env, _, _, _, _, _, _, _, hlb, .store hx, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item =>
      exact .store (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item)
  | env, _, _, _, _, _, _, _, hlb, .load hx, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl =>
      exact .load (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item) hl
  | env, _, _, _, _, _, _, _, hlb, .hint _ hx, henv, hce, ev => by
    simp only [literalsBounded] at hlb
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht =>
      exact .hint (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item) ht
  | env, _, _, _, _, _, _, _, hlb, .neg hx, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop =>
      exact .neg (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb hx henv hce item) hop
  | env, _, _, _, _, _, _, _, hlb, .binary hl hr, henv, hce, ev => by
    simp only [literalsBounded, Bool.and_eq_true] at hlb
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | binary evL evR hop =>
      have evL' := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hl henv hce evL
      have hext := evL'.heap_extends
      have evR' := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.2 hr
        (henv.mono hext hext.length_le) hce evR
      exact .binary evL' evR' hop
  | env, Γ, locals, .call nm (some []) xs, t, h, h', r, hlb, .call hsig items, henv, hce, ev => by
    simp only [Peephole.lowerByteShifts] at ev
    have hlbXs := literalsBounded_call_args hlb
    have hlbXs' := literalsBounded_lowerByteShiftsList env hlbXs
    have htyCall' : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ
        (.call nm (some []) (Peephole.lowerByteShiftsList env xs)) t :=
      .call hsig (hasTy_lowerByteShiftsList hSigs env items)
    have evCall' : EvalExpr world [] locals
        (qualifyExprF F (.call nm (some []) (Peephole.lowerByteShiftsList env xs))) h r h' := by
      cases htr : Peephole.tryLowerByteShift env nm (some []) (Peephole.lowerByteShiftsList env xs) with
      | none => simpa [htr] using ev
      | some e' =>
        rw [htr, Option.getD_some] at ev
        have hlbCall' : literalsBounded (.call nm (some []) (Peephole.lowerByteShiftsList env xs)) = true := by
          unfold Peephole.tryLowerByteShift at htr
          split at htr
          · next x' c' heq => rw [heq]; simpa [literalsBounded, heq] using hlbXs'
          · cases htr
        exact evalExpr_tryLowerByteShift_backward hnd hHas hProv hLib spec hWT hSigs
          htr hlbCall' htyCall' henv hce ev
    rw [qualifyExprF_call] at evCall' ⊢
    cases evCall' with | call evArgs hfn =>
      exact .call
        (evalArgs_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlbXs items henv hce evArgs) hfn
  | env, Γ, locals, .letValue p v b, _, h, h', r, hlb, .letValue (tx := tv) (Δ := Δ) hv hp hb,
      henv, hce, ev => by
    simp only [literalsBounded, Bool.and_eq_true] at hlb
    cases p with
    | bind nm =>
      cases hp
      simp only [Peephole.lowerByteShifts] at ev
      rw [qualifyExprF_letValue] at ev ⊢
      cases ev with | letValue evV' hm evB' =>
        rename_i inp _ _
        have evV := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hv henv hce evV'
        have hokV := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hv henv evV
        have hext := evV.heap_extends
        have hbs := patHasTy_matchPattern .bind hokV hm
        have henvB := envOk_append hbs (henv.mono hext hext.length_le)
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
        subst hm
        have hceB : ConstEnvOk
            (match Peephole.extractU32Const? env (Peephole.lowerByteShifts env v) with
             | some k => (nm, k) :: Peephole.envRemove [nm] env
             | none => Peephole.envRemove [nm] env)
            ([(nm, inp)] ++ locals) ([(nm, tv)] ++ Γ) := by
          cases hcext : Peephole.extractU32Const? env (Peephole.lowerByteShifts env v) with
          | none =>
            exact constEnvOk_envRemove (by simp) (by simp) hce
          | some k =>
            refine constEnvOk_cons_val hce fun htv => ?_
            subst htv
            have hlbV' := literalsBounded_lowerByteShifts env hlb.1
            have htyV' := hasTy_lowerByteShifts hSigs env hv
            exact (evalExpr_extractU32Const?_sound spec hcext hlbV' htyV' hce evV').1
        exact .letValue evV (by simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
          World.matchPattern, matchPatternWith])
          (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs _ hlb.2 hb henvB hceB evB')
    | wildcard | literal _ | tuple _ | array _ | construct _ _ _ =>
      simp only [Peephole.lowerByteShifts] at ev
      rw [qualifyExprF_letValue] at ev ⊢
      cases ev with | letValue evV' hm evB' =>
        rename_i _ _ bs
        have evV := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hv henv hce evV'
        have hokV := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hv henv evV
        have hext := evV.heap_extends
        have hbs := patHasTy_matchPattern hp hokV hm
        have henvB := envOk_append hbs (henv.mono hext hext.length_le)
        have hdomB := matchPattern_names_of_simple hp.isSimple hm
        have hceB := constEnvOk_envRemove hdomB hp.dom_eq hce
        rw [patBoundVars_eq_patBoundNames hp.isSimple] at hceB
        exact .letValue evV hm
          (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs _ hlb.2 hb henvB hceB evB')
    | global _ _ | load _ | orElse _ _ _ | «repeat» _ _ | record _ _ | constructAs _ _ _ _ => cases hp
  | env, Γ, locals, .matchValue s arms, _, h, h', r, hlb, .matchValue hs harms, henv, hce, ev => by
    simp only [literalsBounded, Bool.and_eq_true] at hlb
    simp only [Peephole.lowerByteShifts, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | matchValue evS' hsel evB' =>
      rename_i _ _ bindings _
      have evS := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hs henv hce evS'
      have hokS := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hs henv evS
      have hext := evS.heap_extends
      rw [map_qualifyArmsF, lowerByteShiftsArms_eq_map, List.map_map] at hsel
      have hsel' : SourceSemantics.selectArm world [] _ _
          (arms.map fun arm => (qualifyPatF F arm.1,
            qualifyExprF F (Peephole.lowerByteShifts (Peephole.envRemove (Peephole.patBoundNames arm.1) env) arm.2))) =
          .ok (some (bindings, _)) := hsel
      obtain ⟨p, b, hmem, rfl, hm, hselOrig⟩ :=
        selectArm_mapBody (fun p b => Peephole.lowerByteShifts (Peephole.envRemove (Peephole.patBoundNames p) env) b) hsel'
      obtain ⟨Δ, hp, hb⟩ := harms.mem hmem
      have hlbB := literalsBounded_mem_arms hlb.2 hmem
      have hbs := patHasTy_matchPattern hp hokS hm
      have henvB := envOk_append hbs (henv.mono hext hext.length_le)
      have hdomB := matchPattern_names_of_simple hp.isSimple hm
      have hceB : ConstEnvOk (Peephole.envRemove (Peephole.patBoundNames p) env) (bindings ++ locals) (Δ ++ Γ) := by
        rw [← patBoundVars_eq_patBoundNames hp.isSimple]
        exact constEnvOk_envRemove hdomB hp.dom_eq hce
      rw [← map_qualifyArmsF] at hselOrig
      exact .matchValue evS hselOrig
        (evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs _ hlbB hb henvB hceB evB')
termination_by _ _ _ e _ _ _ _ _ _ _ _ _ => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_lowerByteShifts_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {locals : Environment F Nat}
      {xs : List Expr} {ts : List Lower.Ty} {h h' : Heap F} {vs : List (SourceValue F)},
      literalsBoundedList xs = true →
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      EnvOk enums h h.length Γ locals →
      ConstEnvOk env locals Γ →
      EvalArgs world [] locals ((Peephole.lowerByteShiftsList env xs).map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h'
  | _, _, _, _, _, _, _, _, _, .nil, _, _, ev => by cases ev; exact .nil
  | env, _, _, _, _, _, _, _, hlb, .cons hd tl, henv, hce, ev => by
    simp only [literalsBoundedList, Bool.and_eq_true] at hlb
    cases ev with | cons evH evT =>
      have evH' := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hd henv hce evH
      have hext := evH'.heap_extends
      exact .cons evH'
        (evalArgs_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs env hlb.2 tl
          (henv.mono hext hext.length_le) hce evT)
termination_by _ _ _ xs _ _ _ _ _ _ _ _ _ => sizeOf xs

end

end LowerByteShiftsEval

/-! ### Part 6C: Phase 1 (`Peephole.fuseExpr`) Syntactic, Typing, & Backward Soundness -/

section FuseExprHelpers

theorem matchAdd_eq {e a b : Expr} (h : Peephole.matchAdd e = some (a, b)) :
    e = .call "UInt32::add" (some []) [a, b] := by
  unfold Peephole.matchAdd at h; split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · cases h

theorem matchXor_eq {e a b : Expr} (h : Peephole.matchXor e = some (a, b)) :
    e = .call "UInt32::xor" (some []) [a, b] := by
  unfold Peephole.matchXor at h; split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · cases h

theorem matchOr_eq {e a b : Expr} (h : Peephole.matchOr e = some (a, b)) :
    e = .call "UInt32::or" (some []) [a, b] := by
  unfold Peephole.matchOr at h; split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · cases h

theorem matchShiftConst_inv {env : Peephole.ConstEnv} {e x : Expr} {isR : Bool} {k : Nat}
    (h : Peephole.matchShiftConst env e = some (isR, x, k)) :
    ∃ nm c k0,
      e = .call nm (some []) [x, c] ∧
      Peephole.extractU32Const? env c = some k0 ∧
      k = k0 % 32 ∧
      ((isR = true ∧ Peephole.isShrName nm = true) ∨
       (isR = false ∧ Peephole.isShlName nm = true)) := by
  unfold Peephole.matchShiftConst at h; split at h
  · next nm a c =>
    split at h
    · next hshr =>
      cases hc : Peephole.extractU32Const? env c with
      | none => simp [hc] at h
      | some k0 =>
        rw [hc] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨nm, c, k0, rfl, hc, rfl, Or.inl ⟨rfl, hshr⟩⟩
    · split at h
      · next hshl =>
        cases hc : Peephole.extractU32Const? env c with
        | none => simp [hc] at h
        | some k0 =>
          rw [hc] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨nm, c, k0, rfl, hc, rfl, Or.inr ⟨rfl, hshl⟩⟩
      · cases h
  · cases h

theorem matchRotPair_inv {env : Peephole.ConstEnv} {e1 e2 x : Expr} {kShr kShl : Nat}
    (h : Peephole.matchRotPair env e1 e2 = some (x, kShr, kShl)) :
    Peephole.isHeapPure x = true ∧
    ((Peephole.matchShiftConst env e1 = some (true, x, kShr) ∧
      Peephole.matchShiftConst env e2 = some (false, x, kShl)) ∨
     (Peephole.matchShiftConst env e1 = some (false, x, kShl) ∧
      Peephole.matchShiftConst env e2 = some (true, x, kShr))) := by
  unfold Peephole.matchRotPair at h; split at h
  · next x1 k1 x2 k2 h1 h2 =>
    split at h
    · next hcond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond; obtain ⟨rfl, hp⟩ := hcond
      exact ⟨hp, Or.inl ⟨h1, h2⟩⟩
    · cases h
  · next x1 k1 x2 k2 h1 h2 =>
    split at h
    · next hcond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond; obtain ⟨rfl, hp⟩ := hcond
      exact ⟨hp, Or.inr ⟨h1, h2⟩⟩
    · cases h
  · cases h

theorem rotrFnOf?_inv {kShr kShl : Nat} {nm : String}
    (h : Peephole.rotrFnOf? kShr kShl = some nm) :
    (kShr = 16 ∧ kShl = 16 ∧ nm = "UInt32::rotr16") ∨
    (kShr = 8 ∧ kShl = 24 ∧ nm = "UInt32::rotr8") := by
  unfold Peephole.rotrFnOf? at h; split at h
  · simp only [Option.some.injEq] at h; exact Or.inl ⟨rfl, rfl, h.symm⟩
  · simp only [Option.some.injEq] at h; exact Or.inr ⟨rfl, rfl, h.symm⟩
  · cases h

theorem xorRotrFnOf?_inv {kShr kShl : Nat} {nm : String}
    (h : Peephole.xorRotrFnOf? kShr kShl = some nm) :
    (kShr = 12 ∧ kShl = 20 ∧ nm = "UInt32::xor_rotr12") ∨
    (kShr = 7 ∧ kShl = 25 ∧ nm = "UInt32::xor_rotr7") := by
  unfold Peephole.xorRotrFnOf? at h; split at h
  · simp only [Option.some.injEq] at h; exact Or.inl ⟨rfl, rfl, h.symm⟩
  · simp only [Option.some.injEq] at h; exact Or.inr ⟨rfl, rfl, h.symm⟩
  · cases h

theorem isVarPair_inv {a b : String} {o1 o2 : Expr}
    (h : Peephole.isVarPair a b o1 o2 = true) :
    (o1 = .var a ∧ o2 = .var b) ∨ (o1 = .var b ∧ o2 = .var a) := by
  simp only [Peephole.isVarPair, Lower.vE, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- Helper: `hasBoundVar` on a `tryFuseCall` result is a subset of the original args' bound vars. -/
theorem hasBoundVar_tryFuseCall_sub {env : Peephole.ConstEnv} {nm : String}
    {targs : Option (List Lower.Ty)} {xs : List Expr} {e' : Expr} {v : String}
    (htr : Peephole.tryFuseCall env nm targs xs = some e')
    (hb : hasBoundVar v e' = true) :
    hasBoundVarList v xs = true := by
  unfold Peephole.tryFuseCall at htr; split at htr
  · next a b =>
    split at htr
    · cases ha : Peephole.matchAdd a with
      | some pab =>
        rcases pab with ⟨x, y⟩; rw [ha] at htr; simp only [Option.some.injEq] at htr; subst htr
        rw [matchAdd_eq ha]
        simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false, Bool.or_eq_true] at hb ⊢
        rcases hb with hx | hy | hbb
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr hy)
        · exact Or.inr hbb
      | none =>
        rw [ha] at htr; dsimp only at htr
        cases hbm : Peephole.matchAdd b with
        | none => simp [hbm] at htr
        | some pyz =>
          rcases pyz with ⟨y, z⟩; rw [hbm] at htr; simp only [Option.some.injEq] at htr; subst htr
          rw [matchAdd_eq hbm]
          simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false, Bool.or_eq_true] at hb ⊢
          rcases hb with ha' | hy | hz
          · exact Or.inl ha'
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr hz)
    · split at htr
      · cases hr : Peephole.matchRotPair env a b with
        | none => simp [hr] at htr
        | some tr =>
          rcases tr with ⟨x, k1, k2⟩; rw [hr] at htr; dsimp only at htr
          have ⟨_, hpair⟩ := matchRotPair_inv hr
          have hxIn : hasBoundVar v x = true → hasBoundVarList v [a, b] = true := by
            intro hvx
            rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
              · obtain ⟨_, _, _, rfl, _, _, _⟩ := matchShiftConst_inv h1
                simp [hasBoundVarList, hasBoundVar, hvx]
          cases hrot : Peephole.rotrFnOf? k1 k2 with
          | some rnm =>
            rw [hrot] at htr; simp only [Option.some.injEq] at htr; subst htr
            simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false] at hb
            exact hxIn hb
          | none =>
            rw [hrot] at htr; dsimp only at htr
            cases hxr : Peephole.xorRotrFnOf? k1 k2 with
            | none => simp [hxr] at htr
            | some xfn =>
              cases hxor : Peephole.matchXor x with
              | none => simp [hxr, hxor] at htr
              | some puv =>
                rcases puv with ⟨u, w⟩; rw [hxr, hxor] at htr
                simp only [Option.some.injEq] at htr; subst htr
                simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false] at hb
                exact hxIn (by rw [matchXor_eq hxor]; simpa [hasBoundVar, hasBoundVarList] using hb)
      · split at htr
        · cases b with
          | var vn =>
            dsimp only at htr
            cases hl : env.lookup vn with
            | none => simp [hl] at htr
            | some k =>
              rw [hl] at htr; simp only [Option.some.injEq] at htr; subst htr
              simp only [Lower.callE, Lower.litE, hasBoundVar, hasBoundVarList, Bool.or_false] at hb ⊢
              exact hb
          | _ => cases htr
        · cases htr
  · cases htr

/-- Helper: `hasBoundVar` on a `tryFuseLet` result is a subset of `.letValue (.bind nm) val body`. -/
theorem hasBoundVar_tryFuseLet_sub {env : Peephole.ConstEnv} {nm : String} {val body e' : Expr} {v : String}
    (htr : Peephole.tryFuseLet env nm val body = some e')
    (hb : hasBoundVar v e' = true) :
    hasBoundVar v (.letValue (.bind nm) val body) = true := by
  have ofVal : hasBoundVar v val = true → hasBoundVar v (.letValue (.bind nm) val body) = true :=
    fun h => by simp [hasBoundVar, h]
  have ofBody : hasBoundVar v body = true → hasBoundVar v (.letValue (.bind nm) val body) = true :=
    fun h => by simp [hasBoundVar, h]
  unfold Peephole.tryFuseLet at htr
  cases h1 : Peephole.tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at htr; simp only [Option.some.injEq] at htr; subst htr
    unfold Peephole.tryDropDeadConst at h1
    cases hc : Peephole.extractU32Const? env val with
    | none => simp [hc] at h1
    | some _ =>
      rw [hc] at h1; dsimp only at h1; split at h1
      · simp only [Option.some.injEq] at h1; subst h1; exact ofBody hb
      · cases h1
  | none =>
    rw [h1] at htr
    cases h2 : Peephole.tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at htr; simp only [Option.some.injEq] at htr; subst htr
      unfold Peephole.tryFuseLetAdd3 at h2
      cases ha : Peephole.matchAdd val with
      | none => simp [ha] at h2
      | some pab =>
        rcases pab with ⟨a, b⟩; rw [ha] at h2; dsimp only at h2
        have hval := matchAdd_eq ha
        split at h2
        · next y rhs rest =>
          cases hr : Peephole.matchAdd rhs with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            have hrhs := matchAdd_eq hr
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              rw [hval, hrhs]
              simp only [Lower.letE, Lower.callE, hasBoundVar, hasBoundVarList, patBoundVars,
                Bool.or_false, Bool.or_eq_true] at hb ⊢
              rcases hb with (hy | (ha' | hb' | hq')) | hrest
              · exact Or.inr (Or.inl (Or.inl hy))
              · exact Or.inl (Or.inr (Or.inl ha'))
              · exact Or.inl (Or.inr (Or.inr hb'))
              · exact Or.inr (Or.inl (Or.inr (Or.inr hq')))
              · exact Or.inr (Or.inr hrest)
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                rw [hval, hrhs]
                simp only [Lower.letE, Lower.callE, hasBoundVar, hasBoundVarList, patBoundVars,
                  Bool.or_false, Bool.or_eq_true] at hb ⊢
                rcases hb with (hy | (hp' | ha' | hb')) | hrest
                · exact Or.inr (Or.inl (Or.inl hy))
                · exact Or.inr (Or.inl (Or.inr (Or.inl hp')))
                · exact Or.inl (Or.inr (Or.inl ha'))
                · exact Or.inl (Or.inr (Or.inr hb'))
                · exact Or.inr (Or.inr hrest)
              · cases h2
        · cases hr : Peephole.matchAdd body with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            have hbody := matchAdd_eq hr
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              rw [hval, hbody]
              simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false, Bool.or_eq_true] at hb ⊢
              rcases hb with ha' | hb' | hq'
              · exact Or.inl (Or.inr (Or.inl ha'))
              · exact Or.inl (Or.inr (Or.inr hb'))
              · exact Or.inr (Or.inr hq')
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                rw [hval, hbody]
                simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false, Bool.or_eq_true] at hb ⊢
                rcases hb with hp' | ha' | hb'
                · exact Or.inr (Or.inl hp')
                · exact Or.inl (Or.inr (Or.inl ha'))
                · exact Or.inl (Or.inr (Or.inr hb'))
              · cases h2
    | none =>
      rw [h2] at htr
      cases h3 : Peephole.tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at htr; simp only [Option.some.injEq] at htr; subst htr
        unfold Peephole.tryFuseLetRotr at h3
        cases hs1 : Peephole.matchShiftConst env val with
        | none => simp [hs1] at h3
        | some t1 =>
          rcases t1 with ⟨d1, x1, k1⟩; rw [hs1] at h3; dsimp only at h3
          obtain ⟨_, _, _, hval, _, _, _⟩ := matchShiftConst_inv hs1
          split at h3
          · cases h3
          · split at h3
            · next s2 val2 body2 =>
              split at h3
              · cases h3
              · cases hs2 : Peephole.matchShiftConst env val2 with
                | none => simp [hs2] at h3
                | some t2 =>
                  rcases t2 with ⟨d2, x2, k2⟩; rw [hs2] at h3; dsimp only at h3
                  split at h3
                  · cases h3
                  · cases hrot : Peephole.rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                    | none => simp [hrot] at h3
                    | some rnm =>
                      rw [hrot] at h3; dsimp only at h3
                      split at h3
                      · next y rhs rest =>
                        cases hor : Peephole.matchOr rhs with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            rw [hval]
                            simp only [Lower.letE, Lower.callE, hasBoundVar, hasBoundVarList,
                              patBoundVars, Bool.or_false, Bool.or_eq_true] at hb ⊢
                            rcases hb with (hy | hx1) | hrest
                            · exact Or.inr (Or.inr (Or.inl (Or.inl hy)))
                            · exact Or.inl (Or.inr (Or.inl hx1))
                            · exact Or.inr (Or.inr (Or.inr hrest))
                          · cases h3
                      · cases hor : Peephole.matchOr body2 with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false] at hb
                            exact ofVal (by rw [hval]; simp [hasBoundVar, hasBoundVarList, hb])
                          · cases h3
            · cases h3
      | none =>
        rw [h3] at htr
        cases h4 : Peephole.tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at htr; simp only [Option.some.injEq] at htr; subst htr
          unfold Peephole.tryFuseLetXorRotr4 at h4; split at h4
          · next a b s1 val1 s2 val2 body2 hx =>
            have hval := matchXor_eq hx
            split at h4
            · cases h4
            · split at h4
              · next d1 _ k1 d2 _ k2 _ _ =>
                split at h4
                · cases h4
                · dsimp only at h4
                  cases hxr : Peephole.xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                  | none => simp [hxr] at h4
                  | some xfn =>
                    rw [hxr] at h4; dsimp only at h4
                    split at h4
                    · next y rhs rest =>
                      cases hor : Peephole.matchOr rhs with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          rw [hval]
                          simp only [Lower.letE, Lower.callE, hasBoundVar, hasBoundVarList,
                            patBoundVars, Bool.or_false, Bool.or_eq_true] at hb ⊢
                          rcases hb with (hy | (ha' | hb')) | hrest
                          · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hy))))
                          · exact Or.inl (Or.inr (Or.inl ha'))
                          · exact Or.inl (Or.inr (Or.inr hb'))
                          · exact Or.inr (Or.inr (Or.inr (Or.inr hrest)))
                        · cases h4
                    · cases hor : Peephole.matchOr body2 with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false] at hb
                          exact ofVal (by rw [hval]; simpa [hasBoundVar, hasBoundVarList] using hb)
                        · cases h4
              · cases h4
          · cases h4
        | none =>
          rw [h4] at htr
          unfold Peephole.tryFuseLetXorRotrHalf at htr
          cases hx : Peephole.matchXor val with
          | none => simp [hx] at htr
          | some pab =>
            rcases pab with ⟨a, b⟩; rw [hx] at htr; dsimp only at htr
            have hval := matchXor_eq hx
            split at htr
            · next y rhs rest =>
              cases hor : Peephole.matchOr rhs with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rw [hval]
                      simp only [Lower.letE, Lower.callE, hasBoundVar, hasBoundVarList,
                        patBoundVars, Bool.or_false, Bool.or_eq_true] at hb ⊢
                      rcases hb with (hy | (ha' | hb')) | hrest
                      · exact Or.inr (Or.inl (Or.inl hy))
                      · exact Or.inl (Or.inr (Or.inl ha'))
                      · exact Or.inl (Or.inr (Or.inr hb'))
                      · exact Or.inr (Or.inr hrest)
            · cases hor : Peephole.matchOr body with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      simp only [Lower.callE, hasBoundVar, hasBoundVarList, Bool.or_false] at hb
                      exact ofVal (by rw [hval]; simpa [hasBoundVar, hasBoundVarList] using hb)

mutual

/-- `Peephole.fuseExpr` never introduces any new bound variables! -/
theorem hasBoundVar_fuseExpr_sub (v : String) :
    ∀ (env : Peephole.ConstEnv) (e : Expr),
      hasBoundVar v (Peephole.fuseExpr env e) = true → hasBoundVar v e = true
  | _, .literal _, h | _, .var _, h | _, .global _ _, h | _, .control _ _, h => by
    simp [Peephole.fuseExpr, hasBoundVar] at h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => hasBoundVarList_fuseExpr_sub v env xs h
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h =>
    hasBoundVar_fuseExpr_sub v env x h
  | env, .binary _ l r, h => by
    simp only [Peephole.fuseExpr, hasBoundVar, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_fuseExpr_sub v env l h1)
    · exact Or.inr (hasBoundVar_fuseExpr_sub v env r h2)
  | env, .matchValue s arms, h => by
    simp only [Peephole.fuseExpr, hasBoundVar, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_fuseExpr_sub v env s h1)
    · exact Or.inr (hasBoundVarArms_fuseExpr_sub v env arms h2)
  | env, .call nm targs xs, h => by
    simp only [Peephole.fuseExpr] at h
    cases htr : Peephole.tryFuseCall env nm targs (Peephole.fuseList env xs) with
    | none =>
      rw [htr, Option.getD_none] at h
      exact hasBoundVarList_fuseExpr_sub v env xs h
    | some e' =>
      rw [htr, Option.getD_some] at h
      exact hasBoundVarList_fuseExpr_sub v env xs (hasBoundVar_tryFuseCall_sub htr h)
  | env, .letValue p x b, h => by
    cases p with
    | bind nm =>
      simp only [Peephole.fuseExpr] at h
      let env' : Peephole.ConstEnv :=
        match Peephole.extractU32Const? env (Peephole.fuseExpr env x) with
        | some k => (nm, k) :: Peephole.envRemove [nm] env
        | none => Peephole.envRemove [nm] env
      have hlet : hasBoundVar v (.letValue (.bind nm) (Peephole.fuseExpr env x)
          (Peephole.fuseExpr env' b)) = true := by
        cases htr : Peephole.tryFuseLet env nm (Peephole.fuseExpr env x) (Peephole.fuseExpr env' b) with
        | none =>
          change hasBoundVar v ((Peephole.tryFuseLet env nm (Peephole.fuseExpr env x) (Peephole.fuseExpr env' b)).getD _) = true at h
          rw [htr, Option.getD_none] at h; exact h
        | some e' =>
          change hasBoundVar v ((Peephole.tryFuseLet env nm (Peephole.fuseExpr env x) (Peephole.fuseExpr env' b)).getD _) = true at h
          rw [htr, Option.getD_some] at h; exact hasBoundVar_tryFuseLet_sub htr h
      simp only [hasBoundVar, Bool.or_eq_true] at hlet ⊢
      rcases hlet with (h1 | h2) | h3
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (hasBoundVar_fuseExpr_sub v env x h2))
      · exact Or.inr (hasBoundVar_fuseExpr_sub v env' b h3)
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.fuseExpr, hasBoundVar, Bool.or_eq_true] at h ⊢
      rcases h with (h1 | h2) | h3
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (hasBoundVar_fuseExpr_sub v env x h2))
      · exact Or.inr (hasBoundVar_fuseExpr_sub v _ b h3)
termination_by _ e _ => sizeOf e

theorem hasBoundVarList_fuseExpr_sub (v : String) :
    ∀ (env : Peephole.ConstEnv) (xs : List Expr),
      hasBoundVarList v (Peephole.fuseList env xs) = true → hasBoundVarList v xs = true
  | _, [], h => by cases h
  | env, x :: xs, h => by
    simp only [Peephole.fuseList, hasBoundVarList, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_fuseExpr_sub v env x h1)
    · exact Or.inr (hasBoundVarList_fuseExpr_sub v env xs h2)
termination_by _ xs _ => sizeOf xs

theorem hasBoundVarArms_fuseExpr_sub (v : String) :
    ∀ (env : Peephole.ConstEnv) (arms : List (Pat × Expr)),
      hasBoundVarArms v (Peephole.fuseArms env arms) = true → hasBoundVarArms v arms = true
  | _, [], h => by cases h
  | env, (p, b) :: rest, h => by
    simp only [Peephole.fuseArms, hasBoundVarArms, Bool.or_eq_true] at h ⊢
    rcases h with (h1 | h2) | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (hasBoundVar_fuseExpr_sub v _ b h2))
    · exact Or.inr (hasBoundVarArms_fuseExpr_sub v env rest h3)
termination_by _ arms _ => sizeOf arms

end

/-- `allLitsLt` preservation across `tryFuseCall` (for any `bound ≥ 32`). -/
theorem allLitsLt_tryFuseCall {bound : Nat} (hb : 32 ≤ bound) {env : Peephole.ConstEnv}
    {nm : String} {targs : Option (List Lower.Ty)} {xs : List Expr} {e' : Expr}
    (htr : Peephole.tryFuseCall env nm targs xs = some e')
    (hxs : allLitsLtList bound xs = true) :
    allLitsLt bound e' = true := by
  unfold Peephole.tryFuseCall at htr; split at htr
  · next a b =>
    simp only [allLitsLtList, Bool.and_eq_true] at hxs
    obtain ⟨ha, hb', _⟩ := hxs
    split at htr
    · cases hma : Peephole.matchAdd a with
      | some pab =>
        rcases pab with ⟨x, y⟩; rw [hma] at htr; simp only [Option.some.injEq] at htr; subst htr
        rw [matchAdd_eq hma] at ha
        simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at ha
        simp [Lower.callE, allLitsLt, allLitsLtList, ha.1, ha.2.1, hb']
      | none =>
        rw [hma] at htr; dsimp only at htr
        cases hmb : Peephole.matchAdd b with
        | none => simp [hmb] at htr
        | some pyz =>
          rcases pyz with ⟨y, z⟩; rw [hmb] at htr; simp only [Option.some.injEq] at htr; subst htr
          rw [matchAdd_eq hmb] at hb'
          simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hb'
          simp [Lower.callE, allLitsLt, allLitsLtList, ha, hb'.1, hb'.2.1]
    · split at htr
      · cases hr : Peephole.matchRotPair env a b with
        | none => simp [hr] at htr
        | some tr =>
          rcases tr with ⟨x, k1, k2⟩; rw [hr] at htr; dsimp only at htr
          have hxLt : allLitsLt bound x = true := by
            rcases (matchRotPair_inv hr).2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
              · obtain ⟨_, _, _, heq, _, _, _⟩ := matchShiftConst_inv h1
                rw [heq] at ha; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at ha; exact ha.1
          cases hrot : Peephole.rotrFnOf? k1 k2 with
          | some rnm =>
            rw [hrot] at htr; simp only [Option.some.injEq] at htr; subst htr
            simp [Lower.callE, allLitsLt, allLitsLtList, hxLt]
          | none =>
            rw [hrot] at htr; dsimp only at htr
            cases hxr : Peephole.xorRotrFnOf? k1 k2 with
            | none => simp [hxr] at htr
            | some xfn =>
              cases hxor : Peephole.matchXor x with
              | none => simp [hxr, hxor] at htr
              | some puv =>
                rcases puv with ⟨u, w⟩; rw [hxr, hxor] at htr
                simp only [Option.some.injEq] at htr; subst htr
                rw [matchXor_eq hxor] at hxLt
                simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hxLt
                simp [Lower.callE, allLitsLt, allLitsLtList, hxLt.1, hxLt.2.1]
      · split at htr
        · cases b with
          | var vn =>
            dsimp only at htr
            cases hl : env.lookup vn with
            | none => simp [hl] at htr
            | some k =>
              rw [hl] at htr; simp only [Option.some.injEq] at htr; subst htr
              have hlt : k % 32 < bound := lt_of_lt_of_le (Nat.mod_lt k (by omega)) hb
              simp [Lower.callE, Lower.litE, allLitsLt, allLitsLtList, ha, hlt]
          | _ => cases htr
        · cases htr
  · cases htr

/-- `allLitsLt` preservation across `tryFuseLet`. -/
theorem allLitsLt_tryFuseLet {bound : Nat} {env : Peephole.ConstEnv}
    {nm : String} {val body e' : Expr}
    (htr : Peephole.tryFuseLet env nm val body = some e')
    (hv : allLitsLt bound val = true) (hb : allLitsLt bound body = true) :
    allLitsLt bound e' = true := by
  unfold Peephole.tryFuseLet at htr
  cases h1 : Peephole.tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at htr; simp only [Option.some.injEq] at htr; subst htr
    unfold Peephole.tryDropDeadConst at h1
    cases hc : Peephole.extractU32Const? env val with
    | none => simp [hc] at h1
    | some _ =>
      rw [hc] at h1; dsimp only at h1; split at h1
      · simp only [Option.some.injEq] at h1; subst h1; exact hb
      · cases h1
  | none =>
    rw [h1] at htr
    cases h2 : Peephole.tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at htr; simp only [Option.some.injEq] at htr; subst htr
      unfold Peephole.tryFuseLetAdd3 at h2
      cases ha : Peephole.matchAdd val with
      | none => simp [ha] at h2
      | some pab =>
        rcases pab with ⟨a, b⟩; rw [ha] at h2; dsimp only at h2
        rw [matchAdd_eq ha] at hv; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hv
        split at h2
        · next y rhs rest =>
          simp only [allLitsLt, Bool.and_eq_true] at hb
          cases hr : Peephole.matchAdd rhs with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hb
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              simp [Lower.letE, Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1, hb.1.2.1, hb.2]
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                simp [Lower.letE, Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1, hb.1.1, hb.2]
              · cases h2
        · cases hr : Peephole.matchAdd body with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hb
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              simp [Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1, hb.2.1]
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                simp [Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1, hb.1]
              · cases h2
    | none =>
      rw [h2] at htr
      cases h3 : Peephole.tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at htr; simp only [Option.some.injEq] at htr; subst htr
        unfold Peephole.tryFuseLetRotr at h3
        cases hs1 : Peephole.matchShiftConst env val with
        | none => simp [hs1] at h3
        | some t1 =>
          rcases t1 with ⟨d1, x1, k1⟩; rw [hs1] at h3; dsimp only at h3
          obtain ⟨_, _, _, hval, _, _, _⟩ := matchShiftConst_inv hs1
          rw [hval] at hv; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hv
          split at h3
          · cases h3
          · split at h3
            · next s2 val2 body2 =>
              simp only [allLitsLt, Bool.and_eq_true] at hb
              split at h3
              · cases h3
              · cases hs2 : Peephole.matchShiftConst env val2 with
                | none => simp [hs2] at h3
                | some t2 =>
                  rcases t2 with ⟨d2, x2, k2⟩; rw [hs2] at h3; dsimp only at h3
                  split at h3
                  · cases h3
                  · cases hrot : Peephole.rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                    | none => simp [hrot] at h3
                    | some rnm =>
                      rw [hrot] at h3; dsimp only at h3
                      split at h3
                      · next y rhs rest =>
                        have hrest : allLitsLt bound rest = true := by
                          have hb2 := hb.2; simp only [allLitsLt, Bool.and_eq_true] at hb2; exact hb2.2
                        cases hor : Peephole.matchOr rhs with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            simp [Lower.letE, Lower.callE, allLitsLt, allLitsLtList, hv.1, hrest]
                          · cases h3
                      · cases hor : Peephole.matchOr body2 with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            simp [Lower.callE, allLitsLt, allLitsLtList, hv.1]
                          · cases h3
            · cases h3
      | none =>
        rw [h3] at htr
        cases h4 : Peephole.tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at htr; simp only [Option.some.injEq] at htr; subst htr
          unfold Peephole.tryFuseLetXorRotr4 at h4; split at h4
          · next a b s1 val1 s2 val2 body2 hx =>
            rw [matchXor_eq hx] at hv; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hv
            simp only [allLitsLt, Bool.and_eq_true] at hb
            split at h4
            · cases h4
            · split at h4
              · next d1 _ k1 d2 _ k2 _ _ =>
                split at h4
                · cases h4
                · dsimp only at h4
                  cases hxr : Peephole.xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                  | none => simp [hxr] at h4
                  | some xfn =>
                    rw [hxr] at h4; dsimp only at h4
                    split at h4
                    · next y rhs rest =>
                      have hrest : allLitsLt bound rest = true := by
                        have hb2 := hb.2.2; simp only [allLitsLt, Bool.and_eq_true] at hb2; exact hb2.2
                      cases hor : Peephole.matchOr rhs with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          simp [Lower.letE, Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1, hrest]
                        · cases h4
                    · cases hor : Peephole.matchOr body2 with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          simp [Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1]
                        · cases h4
              · cases h4
          · cases h4
        | none =>
          rw [h4] at htr
          unfold Peephole.tryFuseLetXorRotrHalf at htr
          cases hx : Peephole.matchXor val with
          | none => simp [hx] at htr
          | some pab =>
            rcases pab with ⟨a, b⟩; rw [hx] at htr; dsimp only at htr
            rw [matchXor_eq hx] at hv; simp only [allLitsLt, allLitsLtList, Bool.and_eq_true] at hv
            split at htr
            · next y rhs rest =>
              simp only [allLitsLt, Bool.and_eq_true] at hb
              cases hor : Peephole.matchOr rhs with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      simp [Lower.letE, Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1, hb.2]
            · cases hor : Peephole.matchOr body with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      simp [Lower.callE, allLitsLt, allLitsLtList, hv.1, hv.2.1]

mutual

theorem allLitsLt_fuseExpr {bound : Nat} (hb : 32 ≤ bound) :
    ∀ (env : Peephole.ConstEnv) {e : Expr},
      allLitsLt bound e = true → allLitsLt bound (Peephole.fuseExpr env e) = true
  | _, .literal _, h => h
  | _, .var _, _ | _, .global _ _, _ => rfl
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h | env, .control _ x, h =>
    allLitsLt_fuseExpr hb env (e := x) h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => allLitsLt_fuseList hb env h
  | env, .binary _ l r, h => by
    simp only [Peephole.fuseExpr, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_fuseExpr hb env h.1, allLitsLt_fuseExpr hb env h.2⟩
  | env, .matchValue s arms, h => by
    simp only [Peephole.fuseExpr, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_fuseExpr hb env h.1, allLitsLt_fuseArms hb env h.2⟩
  | env, .call nm targs xs, h => by
    simp only [Peephole.fuseExpr]
    have hxs' := allLitsLt_fuseList hb env h
    cases htr : Peephole.tryFuseCall env nm targs (Peephole.fuseList env xs) with
    | none => simpa [allLitsLt] using hxs'
    | some e' =>
      simp only [Option.getD_some]
      exact allLitsLt_tryFuseCall hb htr hxs'
  | env, .letValue p v b, h => by
    simp only [allLitsLt, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      simp only [Peephole.fuseExpr]
      let env' : Peephole.ConstEnv :=
        match Peephole.extractU32Const? env (Peephole.fuseExpr env v) with
        | some k => (nm, k) :: Peephole.envRemove [nm] env
        | none => Peephole.envRemove [nm] env
      have hv' := allLitsLt_fuseExpr hb env h.1
      have hb' := allLitsLt_fuseExpr hb env' h.2
      change allLitsLt bound ((Peephole.tryFuseLet env nm (Peephole.fuseExpr env v)
          (Peephole.fuseExpr env' b)).getD _) = true
      cases htr : Peephole.tryFuseLet env nm (Peephole.fuseExpr env v)
          (Peephole.fuseExpr env' b) with
      | none => simp only [Option.getD_none, allLitsLt, Bool.and_eq_true]; exact ⟨hv', hb'⟩
      | some e' =>
        simp only [Option.getD_some]
        exact allLitsLt_tryFuseLet htr hv' hb'
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.fuseExpr, allLitsLt, Bool.and_eq_true]
      exact ⟨allLitsLt_fuseExpr hb env h.1, allLitsLt_fuseExpr hb _ h.2⟩
termination_by _ e _ => sizeOf e

theorem allLitsLt_fuseList {bound : Nat} (hb : 32 ≤ bound) :
    ∀ (env : Peephole.ConstEnv) {xs : List Expr},
      allLitsLtList bound xs = true → allLitsLtList bound (Peephole.fuseList env xs) = true
  | _, [], _ => rfl
  | env, x :: xs, h => by
    simp only [Peephole.fuseList, allLitsLtList, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_fuseExpr hb env h.1, allLitsLt_fuseList hb env h.2⟩
termination_by _ xs _ => sizeOf xs

theorem allLitsLt_fuseArms {bound : Nat} (hb : 32 ≤ bound) :
    ∀ (env : Peephole.ConstEnv) {arms : List (Pat × Expr)},
      allLitsLtArms bound arms = true → allLitsLtArms bound (Peephole.fuseArms env arms) = true
  | _, [], _ => rfl
  | env, (p, b) :: rest, h => by
    simp only [Peephole.fuseArms, allLitsLtArms, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_fuseExpr hb _ h.1, allLitsLt_fuseArms hb env h.2⟩
termination_by _ arms _ => sizeOf arms

end

theorem literalsBounded_tryFuseCall {env : Peephole.ConstEnv}
    {nm : String} {targs : Option (List Lower.Ty)} {xs : List Expr} {e' : Expr}
    (htr : Peephole.tryFuseCall env nm targs xs = some e')
    (hxs : literalsBoundedList xs = true) :
    literalsBounded e' = true := by
  unfold Peephole.tryFuseCall at htr; split at htr
  · next a b =>
    simp only [literalsBoundedList, Bool.and_eq_true] at hxs
    obtain ⟨ha, hb', _⟩ := hxs
    split at htr
    · cases hma : Peephole.matchAdd a with
      | some pab =>
        rcases pab with ⟨x, y⟩; rw [hma] at htr; simp only [Option.some.injEq] at htr; subst htr
        rw [matchAdd_eq hma] at ha
        simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at ha
        simp [Lower.callE, literalsBounded, literalsBoundedList, ha.1, ha.2.1, hb']
      | none =>
        rw [hma] at htr; dsimp only at htr
        cases hmb : Peephole.matchAdd b with
        | none => simp [hmb] at htr
        | some pyz =>
          rcases pyz with ⟨y, z⟩; rw [hmb] at htr; simp only [Option.some.injEq] at htr; subst htr
          rw [matchAdd_eq hmb] at hb'
          simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hb'
          simp [Lower.callE, literalsBounded, literalsBoundedList, ha, hb'.1, hb'.2.1]
    · split at htr
      · cases hr : Peephole.matchRotPair env a b with
        | none => simp [hr] at htr
        | some tr =>
          rcases tr with ⟨x, k1, k2⟩; rw [hr] at htr; dsimp only at htr
          have hxLb : literalsBounded x = true := by
            rcases (matchRotPair_inv hr).2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
              · obtain ⟨_, _, _, heq, _, _, _⟩ := matchShiftConst_inv h1
                rw [heq] at ha; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at ha
                exact ha.1
          cases hrot : Peephole.rotrFnOf? k1 k2 with
          | some rnm =>
            rw [hrot] at htr; simp only [Option.some.injEq] at htr; subst htr
            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
              simp [Lower.callE, literalsBounded, hxLb]
          | none =>
            rw [hrot] at htr; dsimp only at htr
            cases hxr : Peephole.xorRotrFnOf? k1 k2 with
            | none => simp [hxr] at htr
            | some xfn =>
              cases hxor : Peephole.matchXor x with
              | none => simp [hxr, hxor] at htr
              | some puv =>
                rcases puv with ⟨u, w⟩; rw [hxr, hxor] at htr
                simp only [Option.some.injEq] at htr; subst htr
                rw [matchXor_eq hxor] at hxLb
                simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hxLb
                simp [Lower.callE, literalsBounded, literalsBoundedList, hxLb.1, hxLb.2.1]
      · split at htr
        · cases b with
          | var vn =>
            dsimp only at htr
            cases hl : env.lookup vn with
            | none => simp [hl] at htr
            | some k =>
              rw [hl] at htr; simp only [Option.some.injEq] at htr; subst htr
              have hlt : k % 32 < natLimit := lt_trans (Nat.mod_lt k (by omega)) (by decide)
              simp [Lower.callE, Lower.litE, literalsBounded, literalsBoundedList, allLitsLt, ha, hlt]
          | _ => cases htr
        · cases htr
  · cases htr

theorem literalsBounded_tryFuseLet {env : Peephole.ConstEnv}
    {nm : String} {val body e' : Expr}
    (htr : Peephole.tryFuseLet env nm val body = some e')
    (hv : literalsBounded val = true) (hb : literalsBounded body = true) :
    literalsBounded e' = true := by
  unfold Peephole.tryFuseLet at htr
  cases h1 : Peephole.tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at htr; simp only [Option.some.injEq] at htr; subst htr
    unfold Peephole.tryDropDeadConst at h1
    cases hc : Peephole.extractU32Const? env val with
    | none => simp [hc] at h1
    | some _ =>
      rw [hc] at h1; dsimp only at h1; split at h1
      · simp only [Option.some.injEq] at h1; subst h1; exact hb
      · cases h1
  | none =>
    rw [h1] at htr
    cases h2 : Peephole.tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at htr; simp only [Option.some.injEq] at htr; subst htr
      unfold Peephole.tryFuseLetAdd3 at h2
      cases ha : Peephole.matchAdd val with
      | none => simp [ha] at h2
      | some pab =>
        rcases pab with ⟨a, b⟩; rw [ha] at h2; dsimp only at h2
        rw [matchAdd_eq ha] at hv; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hv
        split at h2
        · next y rhs rest =>
          simp only [literalsBounded, Bool.and_eq_true] at hb
          cases hr : Peephole.matchAdd rhs with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hb
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              simp [Lower.letE, Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1, hb.1.2.1, hb.2]
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                simp [Lower.letE, Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1, hb.1.1, hb.2]
              · cases h2
        · cases hr : Peephole.matchAdd body with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hb
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              simp [Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1, hb.2.1]
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                simp [Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1, hb.1]
              · cases h2
    | none =>
      rw [h2] at htr
      cases h3 : Peephole.tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at htr; simp only [Option.some.injEq] at htr; subst htr
        unfold Peephole.tryFuseLetRotr at h3
        cases hs1 : Peephole.matchShiftConst env val with
        | none => simp [hs1] at h3
        | some t1 =>
          rcases t1 with ⟨d1, x1, k1⟩; rw [hs1] at h3; dsimp only at h3
          obtain ⟨_, _, _, hval, _, _, _⟩ := matchShiftConst_inv hs1
          rw [hval] at hv; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hv
          split at h3
          · cases h3
          · split at h3
            · next s2 val2 body2 =>
              simp only [literalsBounded, Bool.and_eq_true] at hb
              split at h3
              · cases h3
              · cases hs2 : Peephole.matchShiftConst env val2 with
                | none => simp [hs2] at h3
                | some t2 =>
                  rcases t2 with ⟨d2, x2, k2⟩; rw [hs2] at h3; dsimp only at h3
                  split at h3
                  · cases h3
                  · cases hrot : Peephole.rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                    | none => simp [hrot] at h3
                    | some rnm =>
                      rw [hrot] at h3; dsimp only at h3
                      split at h3
                      · next y rhs rest =>
                        have hrest : literalsBounded rest = true := by
                          have hb2 := hb.2; simp only [literalsBounded, Bool.and_eq_true] at hb2; exact hb2.2
                        cases hor : Peephole.matchOr rhs with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                              simp [Lower.letE, Lower.callE, literalsBounded, hv.1, hrest]
                          · cases h3
                      · cases hor : Peephole.matchOr body2 with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                              simp [Lower.callE, literalsBounded, hv.1]
                          · cases h3
            · cases h3
      | none =>
        rw [h3] at htr
        cases h4 : Peephole.tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at htr; simp only [Option.some.injEq] at htr; subst htr
          unfold Peephole.tryFuseLetXorRotr4 at h4; split at h4
          · next a b s1 val1 s2 val2 body2 hx =>
            rw [matchXor_eq hx] at hv; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hv
            simp only [literalsBounded, Bool.and_eq_true] at hb
            split at h4
            · cases h4
            · split at h4
              · next d1 _ k1 d2 _ k2 _ _ =>
                split at h4
                · cases h4
                · dsimp only at h4
                  cases hxr : Peephole.xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                  | none => simp [hxr] at h4
                  | some xfn =>
                    rw [hxr] at h4; dsimp only at h4
                    split at h4
                    · next y rhs rest =>
                      have hrest : literalsBounded rest = true := by
                        have hb2 := hb.2.2; simp only [literalsBounded, Bool.and_eq_true] at hb2; exact hb2.2
                      cases hor : Peephole.matchOr rhs with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                            simp [Lower.letE, Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1, hrest]
                        · cases h4
                    · cases hor : Peephole.matchOr body2 with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                            simp [Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1]
                        · cases h4
              · cases h4
          · cases h4
        | none =>
          rw [h4] at htr
          unfold Peephole.tryFuseLetXorRotrHalf at htr
          cases hx : Peephole.matchXor val with
          | none => simp [hx] at htr
          | some pab =>
            rcases pab with ⟨a, b⟩; rw [hx] at htr; dsimp only at htr
            rw [matchXor_eq hx] at hv; simp only [literalsBounded, literalsBoundedList, Bool.and_eq_true] at hv
            split at htr
            · next y rhs rest =>
              simp only [literalsBounded, Bool.and_eq_true] at hb
              cases hor : Peephole.matchOr rhs with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                        simp [Lower.letE, Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1, hb.2]
            · cases hor : Peephole.matchOr body with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                        simp [Lower.callE, literalsBounded, literalsBoundedList, hv.1, hv.2.1]

mutual

theorem literalsBounded_fuseExpr :
    ∀ (env : Peephole.ConstEnv) {e : Expr},
      literalsBounded e = true → literalsBounded (Peephole.fuseExpr env e) = true
  | _, .literal _, _ | _, .var _, _ | _, .global _ _, _ => rfl
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h | env, .control _ x, h =>
    literalsBounded_fuseExpr env (e := x) h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => literalsBounded_fuseList env h
  | env, .binary _ l r, h => by
    simp only [Peephole.fuseExpr, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_fuseExpr env h.1, literalsBounded_fuseExpr env h.2⟩
  | env, .matchValue s arms, h => by
    simp only [Peephole.fuseExpr, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_fuseExpr env h.1, literalsBounded_fuseArms env h.2⟩
  | env, .call nm targs xs, h => by
    simp only [Peephole.fuseExpr]
    have hxs' := literalsBounded_fuseList env (literalsBounded_call_args h)
    cases htr : Peephole.tryFuseCall env nm targs (Peephole.fuseList env xs) with
    | some e' =>
      simp only [Option.getD_some]
      exact literalsBounded_tryFuseCall htr hxs'
    | none =>
      simp only [Option.getD_none]
      cases targs with
      | none => simpa [literalsBounded] using hxs'
      | some ts =>
        cases ts with
        | cons _ _ => simpa [literalsBounded] using hxs'
        | nil =>
          cases xs with
          | nil => rfl
          | cons x rest =>
            cases rest with
            | cons y rest2 =>
              simp only [Peephole.fuseList, literalsBounded, literalsBoundedList,
                Bool.and_eq_true] at hxs' ⊢
              exact hxs'
            | nil =>
              simp only [Peephole.fuseList, literalsBounded] at h ⊢
              cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
              | true =>
                simp only [h1, ↓reduceIte, Bool.and_eq_true] at h ⊢
                exact ⟨allLitsLt_fuseExpr (by unfold natLimit; omega) env h.1,
                       literalsBounded_fuseExpr env h.2⟩
              | false =>
                simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases h2 : (nm == "UInt32::from_field") with
                | true =>
                  simp only [h2, ↓reduceIte, Bool.and_eq_true] at h ⊢
                  exact ⟨allLitsLt_fuseExpr (by unfold U32.base; omega) env h.1,
                         literalsBounded_fuseExpr env h.2⟩
                | false =>
                  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  exact literalsBounded_fuseExpr env h
  | env, .letValue p v b, h => by
    simp only [literalsBounded, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      simp only [Peephole.fuseExpr]
      let env' : Peephole.ConstEnv :=
        match Peephole.extractU32Const? env (Peephole.fuseExpr env v) with
        | some k => (nm, k) :: Peephole.envRemove [nm] env
        | none => Peephole.envRemove [nm] env
      have hv' := literalsBounded_fuseExpr env h.1
      have hb' := literalsBounded_fuseExpr env' h.2
      change literalsBounded ((Peephole.tryFuseLet env nm (Peephole.fuseExpr env v)
          (Peephole.fuseExpr env' b)).getD _) = true
      cases htr : Peephole.tryFuseLet env nm (Peephole.fuseExpr env v) (Peephole.fuseExpr env' b) with
      | none => simp only [Option.getD_none, literalsBounded, Bool.and_eq_true]; exact ⟨hv', hb'⟩
      | some e' =>
        simp only [Option.getD_some]
        exact literalsBounded_tryFuseLet htr hv' hb'
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.fuseExpr, literalsBounded, Bool.and_eq_true]
      exact ⟨literalsBounded_fuseExpr env h.1, literalsBounded_fuseExpr _ h.2⟩
termination_by _ e _ => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem literalsBounded_fuseList :
    ∀ (env : Peephole.ConstEnv) {xs : List Expr},
      literalsBoundedList xs = true → literalsBoundedList (Peephole.fuseList env xs) = true
  | _, [], _ => rfl
  | env, x :: xs, h => by
    simp only [Peephole.fuseList, literalsBoundedList, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_fuseExpr env h.1, literalsBounded_fuseList env h.2⟩
termination_by _ xs _ => sizeOf xs

theorem literalsBounded_fuseArms :
    ∀ (env : Peephole.ConstEnv) {arms : List (Pat × Expr)},
      literalsBoundedArms arms = true → literalsBoundedArms (Peephole.fuseArms env arms) = true
  | _, [], _ => rfl
  | env, (p, b) :: rest, h => by
    simp only [Peephole.fuseArms, literalsBoundedArms, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_fuseExpr _ h.1, literalsBounded_fuseArms env h.2⟩
termination_by _ arms _ => sizeOf arms

end

/-! #### `HasTy` Preservation for `Peephole.fuseExpr` -/

private theorem hasTy_drop_bind {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {nm : String} {tv tb : Lower.Ty} {b : Expr}
    (hb : HasTy sigs enums ((nm, tv) :: Γ) b tb)
    (hnot : Peephole.occursFree nm b = false) :
    HasTy sigs enums Γ b tb := by
  refine hasTy_envAgree hb fun z hz => ?_
  have hne : z ≠ nm := by
    intro heq; subst heq
    rw [hasFreeVar_eq_occursFree z hb.isClean, hnot] at hz; cases hz
  simp [List.lookup, beq_false_of_ne hne]

private theorem hasTy_drop_bind_under {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {y nm : String} {ty tv tb : Lower.Ty} {b : Expr}
    (hb : HasTy sigs enums ((y, ty) :: (nm, tv) :: Γ) b tb)
    (hcond : (nm == y || !Peephole.occursFree nm b) = true) :
    HasTy sigs enums ((y, ty) :: Γ) b tb := by
  refine hasTy_envAgree hb fun z hz => ?_
  by_cases hzy : z = y
  · subst hzy; simp [List.lookup]
  · simp only [List.lookup, beq_false_of_ne hzy]
    have hznm : z ≠ nm := by
      intro heq; subst heq
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
      rcases hcond with rfl | hnf
      · exact hzy rfl
      · rw [hasFreeVar_eq_occursFree z hb.isClean, hnf] at hz; cases hz
    simp [beq_false_of_ne hznm]

private theorem hasTy_u32Bin_inv {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {nm : String} {a b : Expr} {t : Lower.Ty}
    (hnm : nm = "UInt32::add" ∨ nm = "UInt32::xor" ∨ nm = "UInt32::or")
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (.call nm (some []) [a, b]) t) :
    t = u32Ty ∧
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ a u32Ty ∧
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ b u32Ty := by
  cases hty with | call hsig items =>
  cases items with | cons ha items1 =>
  cases items1 with | cons hb items2 =>
  cases items2
  rcases hnm with rfl | rfl | rfl <;>
    · rw [show qualifyName _ = _ from rfl, sigsWithU32OfField_nonProg fns rfl] at hsig
      injection hsig with hsig; cases hsig; exact ⟨rfl, ha, hb⟩

private theorem hasTy_shift_inv {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) {env : Peephole.ConstEnv} {Γ : TyEnv}
    {e x : Expr} {isR : Bool} {k : Nat} {t : Lower.Ty}
    (hsh : Peephole.matchShiftConst env e = some (isR, x, k))
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t) :
    t = u32Ty ∧ HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ x u32Ty := by
  obtain ⟨nm, c, k0, rfl, _, _, hdir⟩ := matchShiftConst_inv hsh
  cases hty with | call hsig items =>
  cases items with | cons hx items1 =>
  cases items1 with | cons hc items2 =>
  cases items2
  rcases hdir with ⟨_, hshr⟩ | ⟨_, hshl⟩
  · rw [qualifyName_of_isShrName hshr, sigsWithU32OfField_of_ne _ (by decide)] at hsig
    obtain ⟨hpt, rfl⟩ := hSigs.2.1 _ _ hsig
    simp only [List.cons.injEq, and_true] at hpt; obtain ⟨rfl, rfl⟩ := hpt
    exact ⟨rfl, hx⟩
  · rw [qualifyName_of_isShlName hshl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
    obtain ⟨hpt, rfl⟩ := hSigs.2.2.1 _ _ hsig
    simp only [List.cons.injEq, and_true] at hpt; obtain ⟨rfl, rfl⟩ := hpt
    exact ⟨rfl, hx⟩

theorem hasTy_tryFuseCall {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) {env : Peephole.ConstEnv} {Γ : TyEnv}
    {nm : String} {xs : List Expr} {e' : Expr} {t : Lower.Ty}
    (htr : Peephole.tryFuseCall env nm (some []) xs = some e')
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (.call nm (some []) xs) t) :
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e' t := by
  unfold Peephole.tryFuseCall at htr; split at htr
  · next a b _ =>
    split at htr
    · next hadd =>
      simp only [beq_iff_eq] at hadd; subst hadd
      obtain ⟨rfl, ha, hb⟩ := hasTy_u32Bin_inv (Or.inl rfl) hty
      cases hma : Peephole.matchAdd a with
      | some pab =>
        rcases pab with ⟨x, y⟩; rw [hma] at htr; simp only [Option.some.injEq] at htr; subst htr
        rw [matchAdd_eq hma] at ha
        obtain ⟨_, hx, hy⟩ := hasTy_u32Bin_inv (Or.inl rfl) ha
        refine .call (ptys := [u32Ty, u32Ty, u32Ty]) ?_ (.cons hx (.cons hy (.cons hb .nil)))
        rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl,
            sigsWithU32OfField_nonProg fns rfl]; rfl
      | none =>
        rw [hma] at htr; dsimp only at htr
        cases hmb : Peephole.matchAdd b with
        | none => simp [hmb] at htr
        | some pyz =>
          rcases pyz with ⟨y, z⟩; rw [hmb] at htr; simp only [Option.some.injEq] at htr; subst htr
          rw [matchAdd_eq hmb] at hb
          obtain ⟨_, hy, hz⟩ := hasTy_u32Bin_inv (Or.inl rfl) hb
          refine .call (ptys := [u32Ty, u32Ty, u32Ty]) ?_ (.cons ha (.cons hy (.cons hz .nil)))
          rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl,
              sigsWithU32OfField_nonProg fns rfl]; rfl
    · split at htr
      · next hor =>
        simp only [beq_iff_eq] at hor; subst hor
        obtain ⟨rfl, ha, hb⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hty
        cases hr : Peephole.matchRotPair env a b with
        | none => simp [hr] at htr
        | some tr =>
          rcases tr with ⟨x, k1, k2⟩; rw [hr] at htr; dsimp only at htr
          have hx : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ x u32Ty := by
            rcases (matchRotPair_inv hr).2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
              exact (hasTy_shift_inv hSigs h1 ha).2
          cases hrot : Peephole.rotrFnOf? k1 k2 with
          | some rnm =>
            rw [hrot] at htr; simp only [Option.some.injEq] at htr; subst htr
            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
            · refine .call (ptys := [u32Ty]) ?_ (.cons hx .nil)
              rw [show qualifyName "UInt32::rotr16" = "UInt32::rotr16" from rfl,
                  sigsWithU32OfField_nonProg fns rfl]; rfl
            · refine .call (ptys := [u32Ty]) ?_ (.cons hx .nil)
              rw [show qualifyName "UInt32::rotr8" = "UInt32::rotr8" from rfl,
                  sigsWithU32OfField_nonProg fns rfl]; rfl
          | none =>
            rw [hrot] at htr; dsimp only at htr
            cases hxr : Peephole.xorRotrFnOf? k1 k2 with
            | none => simp [hxr] at htr
            | some xfn =>
              cases hxor : Peephole.matchXor x with
              | none => simp [hxr, hxor] at htr
              | some puv =>
                rcases puv with ⟨u, w⟩; rw [hxr, hxor] at htr
                simp only [Option.some.injEq] at htr; subst htr
                rw [matchXor_eq hxor] at hx
                obtain ⟨_, hu, hw⟩ := hasTy_u32Bin_inv (Or.inr (Or.inl rfl)) hx
                rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                · refine .call (ptys := [u32Ty, u32Ty]) ?_ (.cons hu (.cons hw .nil))
                  rw [show qualifyName "UInt32::xor_rotr12" = "UInt32::xor_rotr12" from rfl,
                      sigsWithU32OfField_nonProg fns rfl]; rfl
                · refine .call (ptys := [u32Ty, u32Ty]) ?_ (.cons hu (.cons hw .nil))
                  rw [show qualifyName "UInt32::xor_rotr7" = "UInt32::xor_rotr7" from rfl,
                      sigsWithU32OfField_nonProg fns rfl]; rfl
      · split at htr
        · next hsh =>
          cases b with
          | var vn =>
            dsimp only at htr
            cases hl : env.lookup vn with
            | none => simp [hl] at htr
            | some k =>
              rw [hl] at htr; simp only [Option.some.injEq] at htr; subst htr
              cases hty with | call hsig items =>
              cases items with | @cons _ _ t1 _ _ ha items1 =>
              cases items1 with | @cons _ _ t2 _ _ hb items2 =>
              cases items2
              have hpt : [t1, t2] = [u32Ty, u32Ty] ∧ t = u32Ty := by
                simp only [Bool.or_eq_true] at hsh
                rcases hsh with hshr | hshl
                · rw [qualifyName_of_isShrName hshr, sigsWithU32OfField_of_ne _ (by decide)] at hsig
                  exact hSigs.2.1 _ _ hsig
                · rw [qualifyName_of_isShlName hshl, sigsWithU32OfField_of_ne _ (by decide)] at hsig
                  exact hSigs.2.2.1 _ _ hsig
              obtain ⟨hpts, rfl⟩ := hpt
              injection hpts with h1 htl
              injection htl with h2 _
              subst h1; subst h2
              refine .call hsig (.cons ha (.cons (.call (ptys := [.field]) ?_ (.cons .literal .nil)) .nil))
              rw [show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl,
                  sigsWithU32OfField_u32_of_field]
          | _ => cases htr
        · cases htr
  · cases htr

theorem hasTy_tryFuseLet {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) {env : Peephole.ConstEnv} {Γ : TyEnv}
    {nm : String} {val body e' : Expr} {tv tb : Lower.Ty}
    (htr : Peephole.tryFuseLet env nm val body = some e')
    (hv : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ val tv)
    (hb : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums ((nm, tv) :: Γ) body tb) :
    HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e' tb := by
  unfold Peephole.tryFuseLet at htr
  cases h1 : Peephole.tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at htr; simp only [Option.some.injEq] at htr; subst htr
    unfold Peephole.tryDropDeadConst at h1
    cases hc : Peephole.extractU32Const? env val with
    | none => simp [hc] at h1
    | some _ =>
      rw [hc] at h1; dsimp only at h1; split at h1
      · next hnf =>
        simp only [Option.some.injEq] at h1; subst h1
        simp only [Bool.not_eq_true'] at hnf
        exact hasTy_drop_bind hb hnf
      · cases h1
  | none =>
    rw [h1] at htr
    cases h2 : Peephole.tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at htr; simp only [Option.some.injEq] at htr; subst htr
      unfold Peephole.tryFuseLetAdd3 at h2
      cases ha : Peephole.matchAdd val with
      | none => simp [ha] at h2
      | some pab =>
        rcases pab with ⟨a, b⟩; rw [ha] at h2; dsimp only at h2
        rw [matchAdd_eq ha] at hv
        obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hv
        split at h2
        · next y rhs rest =>
          cases hb with | letValue hrhsTy hpY hrestTy =>
          cases hpY
          cases hr : Peephole.matchAdd rhs with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hrhsTy
            obtain ⟨rfl, hpTy, hqTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hrhsTy
            split at h2
            · next hcond =>
              simp only [Option.some.injEq] at h2; subst h2
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
              have hqTy' := hasTy_drop_bind hqTy hcond.1.2
              have hrestTy' := hasTy_drop_bind_under hrestTy hcond.2
              refine .letValue (.call (ptys := [u32Ty, u32Ty, u32Ty]) ?_
                (.cons haTy (.cons hbTy (.cons hqTy' .nil)))) .bind hrestTy'
              rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl,
                  sigsWithU32OfField_nonProg fns rfl]; rfl
            · split at h2
              · next hcond =>
                simp only [Option.some.injEq] at h2; subst h2
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
                have hpTy' := hasTy_drop_bind hpTy hcond.1.1.2
                have hrestTy' := hasTy_drop_bind_under hrestTy hcond.2
                refine .letValue (.call (ptys := [u32Ty, u32Ty, u32Ty]) ?_
                  (.cons hpTy' (.cons haTy (.cons hbTy .nil)))) .bind hrestTy'
                rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl,
                    sigsWithU32OfField_nonProg fns rfl]; rfl
              · cases h2
        · cases hr : Peephole.matchAdd body with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb
            obtain ⟨rfl, hpTy, hqTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hb
            split at h2
            · next hcond =>
              simp only [Option.some.injEq] at h2; subst h2
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
              have hqTy' := hasTy_drop_bind hqTy hcond.2
              refine .call (ptys := [u32Ty, u32Ty, u32Ty]) ?_
                (.cons haTy (.cons hbTy (.cons hqTy' .nil)))
              rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl,
                  sigsWithU32OfField_nonProg fns rfl]; rfl
            · split at h2
              · next hcond =>
                simp only [Option.some.injEq] at h2; subst h2
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
                have hpTy' := hasTy_drop_bind hpTy hcond.1.2
                refine .call (ptys := [u32Ty, u32Ty, u32Ty]) ?_
                  (.cons hpTy' (.cons haTy (.cons hbTy .nil)))
                rw [show qualifyName "UInt32::add3" = "UInt32::add3" from rfl,
                    sigsWithU32OfField_nonProg fns rfl]; rfl
              · cases h2
    | none =>
      rw [h2] at htr
      cases h3 : Peephole.tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at htr; simp only [Option.some.injEq] at htr; subst htr
        unfold Peephole.tryFuseLetRotr at h3
        cases hs1 : Peephole.matchShiftConst env val with
        | none => simp [hs1] at h3
        | some t1 =>
          rcases t1 with ⟨d1, x1, k1⟩; rw [hs1] at h3; dsimp only at h3
          obtain ⟨rfl, hx1Ty⟩ := hasTy_shift_inv hSigs hs1 hv
          split at h3
          · cases h3
          · split at h3
            · next s2 val2 body2 =>
              cases hb with | letValue hval2Ty hpS2 hbody2Ty =>
              cases hpS2
              split at h3
              · cases h3
              · cases hs2 : Peephole.matchShiftConst env val2 with
                | none => simp [hs2] at h3
                | some t2 =>
                  rcases t2 with ⟨d2, x2, k2⟩; rw [hs2] at h3; dsimp only at h3
                  obtain ⟨rfl, _⟩ := hasTy_shift_inv hSigs hs2 hval2Ty
                  split at h3
                  · cases h3
                  · cases hrot : Peephole.rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                    | none => simp [hrot] at h3
                    | some rnm =>
                      rw [hrot] at h3; dsimp only at h3
                      have hrotTy : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ
                          (Lower.callE rnm [x1]) u32Ty := by
                        rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                        · refine .call (ptys := [u32Ty]) ?_ (.cons hx1Ty .nil)
                          rw [show qualifyName "UInt32::rotr16" = "UInt32::rotr16" from rfl,
                              sigsWithU32OfField_nonProg fns rfl]; rfl
                        · refine .call (ptys := [u32Ty]) ?_ (.cons hx1Ty .nil)
                          rw [show qualifyName "UInt32::rotr8" = "UInt32::rotr8" from rfl,
                              sigsWithU32OfField_nonProg fns rfl]; rfl
                      split at h3
                      · next y rhs rest =>
                        cases hbody2Ty with | letValue hrhsTy hpY hrestTy =>
                        cases hpY
                        cases hor : Peephole.matchOr rhs with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · next hcond =>
                            simp only [Option.some.injEq] at h3; subst h3
                            rw [matchOr_eq hor] at hrhsTy
                            obtain ⟨rfl, _, _⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hrhsTy
                            simp only [Bool.and_eq_true] at hcond
                            have hrest1 := hasTy_drop_bind_under hrestTy hcond.2
                            have hrest2 := hasTy_drop_bind_under hrest1 hcond.1.2
                            exact .letValue hrotTy .bind hrest2
                          · cases h3
                      · cases hor : Peephole.matchOr body2 with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            rw [matchOr_eq hor] at hbody2Ty
                            obtain ⟨rfl, _, _⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hbody2Ty
                            exact hrotTy
                          · cases h3
            · cases h3
      | none =>
        rw [h3] at htr
        cases h4 : Peephole.tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at htr; simp only [Option.some.injEq] at htr; subst htr
          unfold Peephole.tryFuseLetXorRotr4 at h4; split at h4
          · next a b s1 val1 s2 val2 body2 hx =>
            rw [matchXor_eq hx] at hv
            obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inr (Or.inl rfl)) hv
            cases hb with | letValue hval1Ty hpS1 hinner =>
            cases hpS1
            cases hinner with | letValue hval2Ty hpS2 hbody2Ty =>
            cases hpS2
            split at h4
            · cases h4
            · split at h4
              · next d1 _ k1 d2 _ k2 _ _ =>
                split at h4
                · cases h4
                · dsimp only at h4
                  cases hxr : Peephole.xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                  | none => simp [hxr] at h4
                  | some xfn =>
                    rw [hxr] at h4; dsimp only at h4
                    have hxrTy : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ
                        (Lower.callE xfn [a, b]) u32Ty := by
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                      · refine .call (ptys := [u32Ty, u32Ty]) ?_ (.cons haTy (.cons hbTy .nil))
                        rw [show qualifyName "UInt32::xor_rotr12" = "UInt32::xor_rotr12" from rfl,
                            sigsWithU32OfField_nonProg fns rfl]; rfl
                      · refine .call (ptys := [u32Ty, u32Ty]) ?_ (.cons haTy (.cons hbTy .nil))
                        rw [show qualifyName "UInt32::xor_rotr7" = "UInt32::xor_rotr7" from rfl,
                            sigsWithU32OfField_nonProg fns rfl]; rfl
                    split at h4
                    · next y rhs rest =>
                      cases hbody2Ty with | letValue hrhsTy hpY hrestTy =>
                      cases hpY
                      cases hor : Peephole.matchOr rhs with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · next hcond =>
                          simp only [Option.some.injEq] at h4; subst h4
                          rw [matchOr_eq hor] at hrhsTy
                          obtain ⟨rfl, _, _⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hrhsTy
                          simp only [Bool.and_eq_true] at hcond
                          have hrest1 := hasTy_drop_bind_under hrestTy hcond.2
                          have hrest2 := hasTy_drop_bind_under hrest1 hcond.1.2
                          have hrest3 := hasTy_drop_bind_under hrest2 hcond.1.1.2
                          exact .letValue hxrTy .bind hrest3
                        · cases h4
                    · cases hor : Peephole.matchOr body2 with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          rw [matchOr_eq hor] at hbody2Ty
                          obtain ⟨rfl, _, _⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hbody2Ty
                          exact hxrTy
                        · cases h4
              · cases h4
          · cases h4
        | none =>
          rw [h4] at htr
          unfold Peephole.tryFuseLetXorRotrHalf at htr
          cases hx : Peephole.matchXor val with
          | none => simp [hx] at htr
          | some pab =>
            rcases pab with ⟨a, b⟩; rw [hx] at htr; dsimp only at htr
            rw [matchXor_eq hx] at hv
            obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inr (Or.inl rfl)) hv
            split at htr
            · next y rhs rest =>
              cases hb with | letValue hrhsTy hpY hrestTy =>
              cases hpY
              cases hor : Peephole.matchOr rhs with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                rw [matchOr_eq hor] at hrhsTy
                obtain ⟨rfl, _, _⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hrhsTy
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · next hnot =>
                    cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      have hcond : (nm == y || !Peephole.occursFree nm rest) = true := by
                        by_contra hfalse
                        apply hnot
                        simp [Bool.eq_false_iff.mpr hfalse]
                      have hrestTy' := hasTy_drop_bind_under hrestTy hcond
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                      · refine .letValue (.call (ptys := [u32Ty, u32Ty]) ?_ (.cons haTy (.cons hbTy .nil))) .bind hrestTy'
                        rw [show qualifyName "UInt32::xor_rotr12" = "UInt32::xor_rotr12" from rfl,
                            sigsWithU32OfField_nonProg fns rfl]; rfl
                      · refine .letValue (.call (ptys := [u32Ty, u32Ty]) ?_ (.cons haTy (.cons hbTy .nil))) .bind hrestTy'
                        rw [show qualifyName "UInt32::xor_rotr7" = "UInt32::xor_rotr7" from rfl,
                            sigsWithU32OfField_nonProg fns rfl]; rfl
            · cases hor : Peephole.matchOr body with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                rw [matchOr_eq hor] at hb
                obtain ⟨rfl, _, _⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hb
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                      · refine .call (ptys := [u32Ty, u32Ty]) ?_ (.cons haTy (.cons hbTy .nil))
                        rw [show qualifyName "UInt32::xor_rotr12" = "UInt32::xor_rotr12" from rfl,
                            sigsWithU32OfField_nonProg fns rfl]; rfl
                      · refine .call (ptys := [u32Ty, u32Ty]) ?_ (.cons haTy (.cons hbTy .nil))
                        rw [show qualifyName "UInt32::xor_rotr7" = "UInt32::xor_rotr7" from rfl,
                            sigsWithU32OfField_nonProg fns rfl]; rfl

theorem fuseList_length (env : Peephole.ConstEnv) :
    ∀ xs : List Expr, (Peephole.fuseList env xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (fuseList_length env xs)

mutual

theorem hasTy_fuseExpr {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t →
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (Peephole.fuseExpr env e) t
  | _, _, _, _, .literal => .literal
  | _, _, _, _, .var hl => .var hl
  | env, _, _, _, .tuple items => .tuple (hasTy_fuseList hSigs env items)
  | env, _, _, _, .array hlen items =>
    .array (by rw [fuseList_length]; exact hlen) (hasTy_fuseList hSigs env items)
  | env, _, _, _, .repeat hx => .repeat (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .index hx => .index (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .project hx hget => .project (hasTy_fuseExpr hSigs env hx) hget
  | env, _, _, _, .slice hnot hx => .slice hnot (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .construct h1 h2 h3 h4 hctor items =>
    .construct h1 h2 h3 h4 hctor (hasTy_fuseList hSigs env items)
  | env, _, _, _, .builtin items => .builtin (hasTy_fuseList hSigs env items)
  | env, _, _, _, .store hx => .store (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .load hx => .load (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .hint hfo hx => .hint hfo (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .neg hx => .neg (hasTy_fuseExpr hSigs env hx)
  | env, _, _, _, .binary hl hr =>
    .binary (hasTy_fuseExpr hSigs env hl) (hasTy_fuseExpr hSigs env hr)
  | env, _, _, _, .call (nm := nm) hsig items => by
    simp only [Peephole.fuseExpr]
    have hcall : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums _
        (.call nm (some []) (Peephole.fuseList env _)) _ :=
      .call hsig (hasTy_fuseList hSigs env items)
    cases htr : Peephole.tryFuseCall env nm (some []) (Peephole.fuseList env _) with
    | none => simpa using hcall
    | some e' => simpa using hasTy_tryFuseCall hSigs htr hcall
  | env, _, _, _, .letValue (p := p) (x := v) (b := b) hv hp hb => by
    cases p with
    | bind nm =>
      cases hp
      simp only [Peephole.fuseExpr]
      have hv' := hasTy_fuseExpr hSigs env hv
      have hb' := hasTy_fuseExpr hSigs
        (match Peephole.extractU32Const? env (Peephole.fuseExpr env v) with
         | some k => (nm, k) :: Peephole.envRemove [nm] env
         | none => Peephole.envRemove [nm] env) hb
      cases htr : Peephole.tryFuseLet env nm (Peephole.fuseExpr env v) (Peephole.fuseExpr _ b) with
      | none => exact .letValue hv' .bind hb'
      | some e' => exact hasTy_tryFuseLet hSigs htr hv' hb'
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.fuseExpr]
      exact .letValue (hasTy_fuseExpr hSigs env hv) hp (hasTy_fuseExpr hSigs _ hb)
  | env, _, _, _, .matchValue hs harms =>
    .matchValue (hasTy_fuseExpr hSigs env hs) (hasTy_fuseArms hSigs env harms)

theorem hasTy_fuseList {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ (Peephole.fuseList env xs) ts
  | _, _, _, _, .nil => .nil
  | env, _, _, _, .cons hd tl =>
    .cons (hasTy_fuseExpr hSigs env hd) (hasTy_fuseList hSigs env tl)

theorem hasTy_fuseArms {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms (sigsWithU32OfField (fnSigsOf fns)) enums Γ ts arms tb →
      HasTyArms (sigsWithU32OfField (fnSigsOf fns)) enums Γ ts (Peephole.fuseArms env arms) tb
  | _, _, _, _, _, .nil => .nil
  | env, _, _, _, _, .cons hp hb tl =>
    .cons hp (hasTy_fuseExpr hSigs _ hb) (hasTy_fuseArms hSigs env tl)

end

end FuseExprHelpers

section FuseExprEval

variable {F : Type} [Field F] [DecidableEq F]

private theorem evalExpr_lift_bind {world : World F} {locals : Environment F Nat}
    {nm : String} {v : SourceValue F} {e : Expr} {h h' : Heap F} {r : SourceValue F}
    (hc : isCleanExpr e = true) (hnot : Peephole.occursFree nm e = false)
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    EvalExpr world [] ((nm, v) :: locals) (qualifyExprF F e) h r h' := by
  refine evalExpr_localsAgree hc (fun z hz => ?_) ev
  have hne : z ≠ nm := by
    intro heq; subst heq; rw [hasFreeVar_eq_occursFree z hc, hnot] at hz; cases hz
  simp [beq_false_of_ne (Ne.symm hne)]

private theorem evalExpr_lift_bind_under {world : World F} {locals : Environment F Nat}
    {y nm : String} {vy v : SourceValue F} {e : Expr} {h h' : Heap F} {r : SourceValue F}
    (hc : isCleanExpr e = true)
    (hcond : (nm == y || !Peephole.occursFree nm e) = true)
    (ev : EvalExpr world [] ((y, vy) :: locals) (qualifyExprF F e) h r h') :
    EvalExpr world [] ((y, vy) :: (nm, v) :: locals) (qualifyExprF F e) h r h' := by
  refine evalExpr_localsAgree hc (fun z hz => ?_) ev
  by_cases hzy : z = y
  · subst hzy; simp
  · simp only [List.find?_cons, beq_false_of_ne (Ne.symm hzy)]
    have hznm : z ≠ nm := by
      intro heq; subst heq
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
      rcases hcond with rfl | hnf
      · exact hzy rfl
      · rw [hasFreeVar_eq_occursFree z hc, hnf] at hz; cases hz
    simp [beq_false_of_ne (Ne.symm hznm)]

/-- Build `EvalExpr` for any matched constant shift `u32_shr(x, c)` or `u32_shl(x, c)`! -/
private theorem evalExpr_shift_mk {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world) (hSigs : HasU32HelperSigs fns)
    {env : Peephole.ConstEnv} {Γ : TyEnv} {locals : Environment F Nat}
    {e x : Expr} {isR : Bool} {k nx : Nat} {vx : SourceValue F} {h h1 : Heap F}
    (hsh : Peephole.matchShiftConst env e = some (isR, x, k))
    (hlb : literalsBounded e = true)
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e u32Ty)
    (hce : ConstEnvOk env locals Γ)
    (evX : EvalExpr world [] locals (qualifyExprF F x) h vx h1)
    (hvx : isU32Val nx vx) :
    ∃ r, EvalExpr world [] locals (qualifyExprF F e) h r h1 ∧
      (if isR then isU32Val (nx >>> k) r else isU32Val ((nx <<< k) % U32.base) r) := by
  obtain ⟨nm, c, k0, rfl, hcext, rfl, hdir⟩ := matchShiftConst_inv hsh
  cases hty with | call hsig items =>
  cases items with | cons _ items1 =>
  cases items1 with | cons hc items2 =>
  cases items2
  have hlbArgs := literalsBounded_call_args hlb
  simp only [literalsBoundedList, Bool.and_eq_true] at hlbArgs
  rw [qualifyExprF_call]
  simp only [Option.map_some, List.map_nil, List.map_cons]
  rcases hdir with ⟨rfl, hshr⟩ | ⟨rfl, hshl⟩
  · have hq := qualifyName_of_isShrName hshr
    rw [hq, sigsWithU32OfField_of_ne _ (by decide)] at hsig
    obtain ⟨hpt, _⟩ := hSigs.2.1 _ _ hsig
    simp only [List.cons.injEq, and_true] at hpt; obtain ⟨rfl, rfl⟩ := hpt
    obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h1 hcext hlbArgs.2.1 hc hce
    have hlt : nx >>> (k0 % 32) < U32.base := by
      rw [Nat.shiftRight_eq_div_pow]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (isU32Val_lt hvx)
    let wr := u32ValOfNat F (nx >>> (k0 % 32))
    have hwr : isU32Val (nx >>> (k0 % 32)) wr := isU32Val_u32ValOfNat hlt
    refine ⟨wr, .call (.cons evX (.cons evC .nil)) ?_, hwr⟩
    rw [hq]
    simpa [instanceName, Instance.symbol] using spec.shr_mk nx k0 vx vc wr h1 hvx (hvc rfl) hwr
  · have hq := qualifyName_of_isShlName hshl
    rw [hq, sigsWithU32OfField_of_ne _ (by decide)] at hsig
    obtain ⟨hpt, _⟩ := hSigs.2.2.1 _ _ hsig
    simp only [List.cons.injEq, and_true] at hpt; obtain ⟨rfl, rfl⟩ := hpt
    obtain ⟨vc, evC, hvc⟩ := evalExpr_extractU32Const?_mk spec h1 hcext hlbArgs.2.1 hc hce
    let wr := u32ValOfNat F ((nx <<< (k0 % 32)) % U32.base)
    have hwr : isU32Val ((nx <<< (k0 % 32)) % U32.base) wr :=
      isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
    refine ⟨wr, .call (.cons evX (.cons evC .nil)) ?_, hwr⟩
    rw [hq]
    simpa [instanceName, Instance.symbol] using spec.shl_mk nx k0 vx vc wr h1 hvx (hvc rfl) hwr

private theorem nat_lor_comm (a b : Nat) : a ||| b = b ||| a := by
  apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]

/-- Build `EvalExpr` for `UInt32::or(e1, e2)` from a matched rotation pair `(x, kShr, kShl)`! -/
private theorem evalExpr_rotPair_mk {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world) (hSigs : HasU32HelperSigs fns)
    {env : Peephole.ConstEnv} {Γ : TyEnv} {locals : Environment F Nat}
    {e1 e2 x : Expr} {kShr kShl nx : Nat} {vx r : SourceValue F} {h : Heap F}
    (hrp : Peephole.matchRotPair env e1 e2 = some (x, kShr, kShl))
    (hlb1 : literalsBounded e1 = true) (hlb2 : literalsBounded e2 = true)
    (hty1 : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e1 u32Ty)
    (hty2 : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e2 u32Ty)
    (hce : ConstEnvOk env locals Γ)
    (evX : EvalExpr world [] locals (qualifyExprF F x) h vx h)
    (hvx : isU32Val nx vx)
    (hr : isU32Val ((nx >>> kShr) ||| ((nx <<< kShl) % U32.base)) r) :
    EvalExpr world [] locals (qualifyExprF F (.call "UInt32::or" (some []) [e1, e2])) h r h := by
  rw [qualifyExprF_call]
  simp only [Option.map_some, List.map_nil, List.map_cons,
    show qualifyName "UInt32::or" = "UInt32::or" from rfl]
  rcases (matchRotPair_inv hrp).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨v1, ev1, hv1⟩ := evalExpr_shift_mk spec hSigs h1 hlb1 hty1 hce evX hvx
    obtain ⟨v2, ev2, hv2⟩ := evalExpr_shift_mk spec hSigs h2 hlb2 hty2 hce evX hvx
    exact .call (.cons ev1 (.cons ev2 .nil))
      (by simpa [instanceName, Instance.symbol] using spec.or_mk _ _ v1 v2 r h hv1 hv2 hr)
  · obtain ⟨v1, ev1, hv1⟩ := evalExpr_shift_mk spec hSigs h1 hlb1 hty1 hce evX hvx
    obtain ⟨v2, ev2, hv2⟩ := evalExpr_shift_mk spec hSigs h2 hlb2 hty2 hce evX hvx
    have hr' : isU32Val (((nx <<< kShl) % U32.base) ||| (nx >>> kShr)) r := by
      rwa [nat_lor_comm]
    exact .call (.cons ev1 (.cons ev2 .nil))
      (by simpa [instanceName, Instance.symbol] using spec.or_mk _ _ v1 v2 r h hv1 hv2 hr')

/-- Backward soundness of `Peephole.tryFuseCall`! -/
theorem evalExpr_tryFuseCall_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns)
    {env : Peephole.ConstEnv} {Γ : TyEnv} {locals : Environment F Nat}
    {nm : String} {xs : List Expr} {e' : Expr} {t : Lower.Ty} {h h' : Heap F} {r : SourceValue F}
    (htr : Peephole.tryFuseCall env nm (some []) xs = some e')
    (hlb : literalsBoundedList xs = true)
    (hty : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (.call nm (some []) xs) t)
    (henv : EnvOk enums h h.length Γ locals)
    (hce : ConstEnvOk env locals Γ)
    (ev : EvalExpr world [] locals (qualifyExprF F e') h r h') :
    EvalExpr world [] locals (qualifyExprF F (.call nm (some []) xs)) h r h' := by
  unfold Peephole.tryFuseCall at htr; split at htr
  · next a b _ =>
    simp only [literalsBoundedList, Bool.and_eq_true] at hlb
    obtain ⟨hlbA, hlbB, _⟩ := hlb
    split at htr
    · next hadd =>
      simp only [beq_iff_eq] at hadd; subst hadd
      obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hty
      cases hma : Peephole.matchAdd a with
      | some pab =>
        rcases pab with ⟨x, y⟩; rw [hma] at htr; simp only [Option.some.injEq] at htr; subst htr
        have haEq := matchAdd_eq hma; subst haEq
        obtain ⟨_, hxTy, hyTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) haTy
        rw [Lower.callE, qualifyExprF_call] at ev
        simp only [Option.map_some, List.map_nil, List.map_cons,
          show qualifyName "UInt32::add3" = "UInt32::add3" from rfl] at ev
        obtain ⟨vx, vy, vb, h1, h2, hm, evX, evY, evB, hfn⟩ := evalExpr_call3_inv ev
        have hokX := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hxTy henv evX
        have hext1 := evX.heap_extends
        have hokY := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hyTy (henv.mono hext1 hext1.length_le) evY
        have hext2 := hext1.trans evY.heap_extends
        have hokB := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henv.mono hext2 hext2.length_le) evB
        obtain ⟨nx, hnx⟩ := (ValOk_u32 ..).mp hokX
        obtain ⟨ny, hny⟩ := (ValOk_u32 ..).mp hokY
        obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp hokB
        obtain ⟨hr, rfl⟩ := spec.peep.add3 nx ny nb vx vy vb hm r h' hnx hny hnb hfn
        let vxy := u32ValOfNat F ((nx + ny) % U32.base)
        have hvxy : isU32Val ((nx + ny) % U32.base) vxy := isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
        have hr' : isU32Val (((nx + ny) % U32.base + nb) % U32.base) r := by
          rwa [Peephole.add3_left_nat]
        rw [qualifyExprF_call]
        simp only [Option.map_some, List.map_nil, List.map_cons,
          show qualifyName "UInt32::add" = "UInt32::add" from rfl]
        refine .call (.cons ?_ (.cons evB .nil))
          (by simpa [instanceName, Instance.symbol] using spec.add_mk _ nb vxy vb r h' hvxy hnb hr')
        rw [qualifyExprF_call]
        simp only [Option.map_some, List.map_nil, List.map_cons,
          show qualifyName "UInt32::add" = "UInt32::add" from rfl]
        exact .call (.cons evX (.cons evY .nil))
          (by simpa [instanceName, Instance.symbol] using spec.add_mk nx ny vx vy vxy h2 hnx hny hvxy)
      | none =>
        rw [hma] at htr; dsimp only at htr
        cases hmb : Peephole.matchAdd b with
        | none => simp [hmb] at htr
        | some pyz =>
          rcases pyz with ⟨y, z⟩; rw [hmb] at htr; simp only [Option.some.injEq] at htr; subst htr
          have hbEq := matchAdd_eq hmb; subst hbEq
          obtain ⟨_, hyTy, hzTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hbTy
          rw [Lower.callE, qualifyExprF_call] at ev
          simp only [Option.map_some, List.map_nil, List.map_cons,
            show qualifyName "UInt32::add3" = "UInt32::add3" from rfl] at ev
          obtain ⟨va, vy, vz, h1, h2, hm, evA, evY, evZ, hfn⟩ := evalExpr_call3_inv ev
          have hokA := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA
          have hext1 := evA.heap_extends
          have hokY := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hyTy (henv.mono hext1 hext1.length_le) evY
          have hext2 := hext1.trans evY.heap_extends
          have hokZ := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hzTy (henv.mono hext2 hext2.length_le) evZ
          obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp hokA
          obtain ⟨ny, hny⟩ := (ValOk_u32 ..).mp hokY
          obtain ⟨nz, hnz⟩ := (ValOk_u32 ..).mp hokZ
          obtain ⟨hr, rfl⟩ := spec.peep.add3 na ny nz va vy vz hm r h' hna hny hnz hfn
          let vyz := u32ValOfNat F ((ny + nz) % U32.base)
          have hvyz : isU32Val ((ny + nz) % U32.base) vyz := isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
          have hr' : isU32Val ((na + (ny + nz) % U32.base) % U32.base) r := by
            rwa [Peephole.add3_right_nat]
          rw [qualifyExprF_call]
          simp only [Option.map_some, List.map_nil, List.map_cons,
            show qualifyName "UInt32::add" = "UInt32::add" from rfl]
          refine .call (.cons evA (.cons ?_ .nil))
            (by simpa [instanceName, Instance.symbol] using spec.add_mk na _ va vyz r h' hna hvyz hr')
          rw [qualifyExprF_call]
          simp only [Option.map_some, List.map_nil, List.map_cons,
            show qualifyName "UInt32::add" = "UInt32::add" from rfl]
          exact .call (.cons evY (.cons evZ .nil))
            (by simpa [instanceName, Instance.symbol] using spec.add_mk ny nz vy vz vyz h' hny hnz hvyz)
    · split at htr
      · next hor =>
        simp only [beq_iff_eq] at hor; subst hor
        obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hty
        cases hr : Peephole.matchRotPair env a b with
        | none => simp [hr] at htr
        | some tr =>
          rcases tr with ⟨x, kShr, kShl⟩; rw [hr] at htr; dsimp only at htr
          obtain ⟨hpX, hpair⟩ := matchRotPair_inv hr
          have hxTy : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ x u32Ty := by
            rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact (hasTy_shift_inv hSigs h1 haTy).2
          cases hrot : Peephole.rotrFnOf? kShr kShl with
          | some rnm =>
            rw [hrot] at htr; simp only [Option.some.injEq] at htr; subst htr
            rw [Lower.callE, qualifyExprF_call] at ev
            simp only [Option.map_some, List.map_nil, List.map_cons] at ev
            obtain ⟨vx, hm, evX, hfn⟩ := evalExpr_call1_inv ev
            have h1 := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hpX hxTy henv evX
            subst h1
            have hokX := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hxTy henv evX
            obtain ⟨nx, hnx⟩ := (ValOk_u32 ..).mp hokX
            rcases rotrFnOf?_inv hrot with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · obtain ⟨hrU, rfl⟩ := spec.peep.rotr16 nx vx hm r h' hnx hfn
              exact evalExpr_rotPair_mk spec hSigs hr hlbA hlbB haTy hbTy hce evX hnx hrU
            · obtain ⟨hrU, rfl⟩ := spec.peep.rotr8 nx vx hm r h' hnx hfn
              exact evalExpr_rotPair_mk spec hSigs hr hlbA hlbB haTy hbTy hce evX hnx hrU
          | none =>
            rw [hrot] at htr; dsimp only at htr
            cases hxr : Peephole.xorRotrFnOf? kShr kShl with
            | none => simp [hxr] at htr
            | some xfn =>
              cases hxor : Peephole.matchXor x with
              | none => simp [hxr, hxor] at htr
              | some puv =>
                rcases puv with ⟨u, w⟩; rw [hxr, hxor] at htr
                simp only [Option.some.injEq] at htr; subst htr
                have hxEq := matchXor_eq hxor; subst hxEq
                obtain ⟨_, huTy, hwTy⟩ := hasTy_u32Bin_inv (Or.inr (Or.inl rfl)) hxTy
                simp only [Peephole.isHeapPure, Peephole.isHeapPureList, Bool.and_eq_true] at hpX
                obtain ⟨_, hpU, hpW, _⟩ := hpX
                rw [Lower.callE, qualifyExprF_call] at ev
                simp only [Option.map_some, List.map_nil, List.map_cons] at ev
                obtain ⟨vu, vw, h1, hm, evU, evW, hfn⟩ := evalExpr_call2_inv ev
                have hh1 := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hpU huTy henv evU
                subst hh1
                have hh2 := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hpW hwTy henv evW
                subst hh2
                obtain ⟨nu, hnu⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT huTy henv evU)
                obtain ⟨nw, hnw⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hwTy henv evW)
                let vxor := u32ValOfNat F (Nat.xor nu nw)
                have hvxor : isU32Val (Nat.xor nu nw) vxor :=
                  isU32Val_u32ValOfNat (Nat.xor_lt_two_pow (n := 32) (isU32Val_lt hnu) (isU32Val_lt hnw))
                have evXor : EvalExpr world [] locals (qualifyExprF F (.call "UInt32::xor" (some []) [u, w])) hm vxor hm := by
                  rw [qualifyExprF_call]
                  simp only [Option.map_some, List.map_nil, List.map_cons,
                    show qualifyName "UInt32::xor" = "UInt32::xor" from rfl]
                  exact .call (.cons evU (.cons evW .nil))
                    (by simpa [instanceName, Instance.symbol] using spec.xor_mk nu nw vu vw vxor hm hnu hnw hvxor)
                rcases xorRotrFnOf?_inv hxr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                · obtain ⟨hrU, rfl⟩ := spec.peep.xor_rotr12 nu nw vu vw hm r h' hnu hnw hfn
                  exact evalExpr_rotPair_mk spec hSigs hr hlbA hlbB haTy hbTy hce evXor hvxor hrU
                · obtain ⟨hrU, rfl⟩ := spec.peep.xor_rotr7 nu nw vu vw hm r h' hnu hnw hfn
                  exact evalExpr_rotPair_mk spec hSigs hr hlbA hlbB haTy hbTy hce evXor hvxor hrU
      · split at htr
        · next hsh =>
          cases b with
          | var vn =>
            dsimp only at htr
            cases hl : env.lookup vn with
            | none => simp [hl] at htr
            | some k =>
              rw [hl] at htr; simp only [Option.some.injEq] at htr; subst htr
              cases hty with | call hsig items =>
              cases items with | cons haTy items1 =>
              cases items1 with | cons hbTy items2 =>
              cases items2
              cases hbTy with | var hΓvn =>
              obtain ⟨vvn, hfound, huVn⟩ := hce vn k hl
              rw [Lower.callE] at ev
              rw [qualifyExprF_call] at ev ⊢
              simp only [Option.map_some, List.map_nil, List.map_cons] at ev ⊢
              obtain ⟨va, vk, h1, h2, evA, evK, hfn⟩ := evalExpr_call2_inv ev
              rw [Lower.callE, Lower.litE, qualifyExprF_call] at evK
              simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_literal,
                show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl] at evK
              obtain ⟨vl, hl1, evL, hfnK⟩ := evalExpr_call1_inv evK
              obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evL
              obtain ⟨⟨k', hk', hfeq, hvk⟩, rfl⟩ := spec.u32_of_field _ _ _ _ hfnK
              have hkEq : k % 32 = k' := spec.fc.natCast_inj56
                (lt_trans (Nat.mod_lt k (by omega)) (by decide)) hk' (Value.field.inj hfeq)
              subst hkEq
              have hvk' : isU32Val (k % 32) vk := by
                rwa [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt k (by omega)) (by decide))] at hvk
              simp only [Bool.or_eq_true] at hsh
              rcases hsh with hshr | hshl
              · have hq := qualifyName_of_isShrName hshr
                rw [hq, sigsWithU32OfField_of_ne _ (by decide)] at hsig
                obtain ⟨hpt, rfl⟩ := hSigs.2.1 _ _ hsig
                simp only [List.cons.injEq, and_true] at hpt; obtain ⟨rfl, rfl⟩ := hpt
                obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA)
                rw [hq] at hfn ⊢
                obtain ⟨hrU, rfl⟩ := spec.peep.shr na (k % 32) va vk h2 r h' hna hvk' hfn
                rw [Nat.mod_mod] at hrU
                refine .call (.cons evA (.cons (by rw [qualifyExprF_var]; exact .var hfound) .nil)) ?_
                simpa [instanceName, Instance.symbol] using
                  spec.shr_mk na k va vvn r h' hna (huVn hΓvn) hrU
              · have hq := qualifyName_of_isShlName hshl
                rw [hq, sigsWithU32OfField_of_ne _ (by decide)] at hsig
                obtain ⟨hpt, rfl⟩ := hSigs.2.2.1 _ _ hsig
                simp only [List.cons.injEq, and_true] at hpt; obtain ⟨rfl, rfl⟩ := hpt
                obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA)
                rw [hq] at hfn ⊢
                obtain ⟨hrU, rfl⟩ := spec.peep.shl na (k % 32) va vk h2 r h' hna hvk' hfn
                rw [Nat.mod_mod] at hrU
                refine .call (.cons evA (.cons (by rw [qualifyExprF_var]; exact .var hfound) .nil)) ?_
                simpa [instanceName, Instance.symbol] using
                  spec.shl_mk na k va vvn r h' hna (huVn hΓvn) hrU
          | _ => cases htr
        · cases htr
  · cases htr

private theorem matchPattern_bind_ok {world : World F} {h : Heap F} (nm : String) (v : SourceValue F) :
    world.matchPattern [] h (qualifyPatF F (.bind nm)) v = .ok (some [(nm, v)]) := by
  simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith]

private theorem evalExpr_let_bind_qual_inv {world : World F} {locals : Environment F Nat}
    {nm : String} {v b : Expr} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F (.letValue (.bind nm) v b)) h r h') :
    ∃ val hm, EvalExpr world [] locals (qualifyExprF F v) h val hm ∧
      EvalExpr world [] ((nm, val) :: locals) (qualifyExprF F b) hm r h' := by
  rw [qualifyExprF_letValue] at ev
  simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map] at ev
  exact evalExpr_let_bind_inv ev

/-- Backward soundness of `Peephole.tryFuseLet`! -/
theorem evalExpr_tryFuseLet_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns)
    {env : Peephole.ConstEnv} {Γ : TyEnv} {locals : Environment F Nat}
    {nm : String} {val body e' : Expr} {tv tb : Lower.Ty} {h h' : Heap F} {r : SourceValue F}
    (htr : Peephole.tryFuseLet env nm val body = some e')
    (hlbV : literalsBounded val = true) (hlbB : literalsBounded body = true)
    (hv : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ val tv)
    (hb : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums ((nm, tv) :: Γ) body tb)
    (henv : EnvOk enums h h.length Γ locals)
    (hce : ConstEnvOk env locals Γ)
    (hnotNm : nm ∉ env.map Prod.fst)
    (hnotB : ∀ s, hasBoundVar s body = true → s ∉ env.map Prod.fst)
    (ev : EvalExpr world [] locals (qualifyExprF F e') h r h') :
    EvalExpr world [] locals (qualifyExprF F (.letValue (.bind nm) val body)) h r h' := by
  unfold Peephole.tryFuseLet at htr
  cases h1 : Peephole.tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at htr; simp only [Option.some.injEq] at htr; subst htr
    unfold Peephole.tryDropDeadConst at h1
    cases hcext : Peephole.extractU32Const? env val with
    | none => simp [hcext] at h1
    | some k =>
      rw [hcext] at h1; dsimp only at h1; split at h1
      · next hnf =>
        simp only [Option.some.injEq] at h1; subst h1
        simp only [Bool.not_eq_true'] at hnf
        obtain ⟨v0, evV, _⟩ := evalExpr_extractU32Const?_mk spec h hcext hlbV hv hce
        rw [qualifyExprF_letValue]
        exact .letValue evV (matchPattern_bind_ok nm v0)
          (evalExpr_lift_bind hb.isClean hnf ev)
      · cases h1
  | none =>
    rw [h1] at htr
    cases h2 : Peephole.tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at htr; simp only [Option.some.injEq] at htr; subst htr
      unfold Peephole.tryFuseLetAdd3 at h2
      cases ha : Peephole.matchAdd val with
      | none => simp [ha] at h2
      | some pab =>
        rcases pab with ⟨a, b⟩; rw [ha] at h2; dsimp only at h2
        have hvalEq := matchAdd_eq ha; subst hvalEq
        obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hv
        split at h2
        · next y rhs rest =>
          cases hb with | letValue hrhsTy hpY hrestTy =>
          cases hpY
          cases hr : Peephole.matchAdd rhs with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            have hrhsEq := matchAdd_eq hr; subst hrhsEq
            obtain ⟨rfl, hpTy, hqTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hrhsTy
            split at h2
            · next hcond =>
              simp only [Option.some.injEq] at h2; subst h2
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
              obtain ⟨⟨rfl, hnfQ⟩, hcondRest⟩ := hcond
              have hqTy' := hasTy_drop_bind hqTy hnfQ
              rw [Lower.letE] at ev
              obtain ⟨vy, h1', evAdd3, evRest⟩ := evalExpr_let_bind_qual_inv ev
              rw [Lower.callE, qualifyExprF_call] at evAdd3
              simp only [Option.map_some, List.map_nil, List.map_cons,
                show qualifyName "UInt32::add3" = "UInt32::add3" from rfl] at evAdd3
              obtain ⟨va, vb, vq, ha1, hb1, hm, evA, evB, evQ, hfn⟩ := evalExpr_call3_inv evAdd3
              obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA)
              have hext1 := evA.heap_extends
              obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henv.mono hext1 hext1.length_le) evB)
              have hext2 := hext1.trans evB.heap_extends
              obtain ⟨nq, hnq⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hqTy' (henv.mono hext2 hext2.length_le) evQ)
              obtain ⟨hvy, rfl⟩ := spec.peep.add3 na nb nq va vb vq hm vy h1' hna hnb hnq hfn
              let vnm := u32ValOfNat F ((na + nb) % U32.base)
              have hvnm : isU32Val ((na + nb) % U32.base) vnm := isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
              have hvy' : isU32Val (((na + nb) % U32.base + nq) % U32.base) vy := by
                rwa [Peephole.add3_left_nat]
              rw [qualifyExprF_letValue, qualifyExprF_call, qualifyExprF_letValue, qualifyExprF_call]
              simp only [Option.map_some, List.map_nil, List.map_cons,
                show qualifyName "UInt32::add" = "UInt32::add" from rfl]
              refine .letValue (.call (.cons evA (.cons evB .nil))
                  (by simpa [instanceName, Instance.symbol] using spec.add_mk na nb va vb vnm hb1 hna hnb hvnm))
                (matchPattern_bind_ok nm vnm) ?_
              have evVar : EvalExpr world [] ((nm, vnm) :: locals) (qualifyExprF F (Lower.vE nm)) hb1 vnm hb1 := by
                rw [Lower.vE, qualifyExprF_var]; exact .var (by simp)
              refine .letValue (.call (.cons evVar (.cons (evalExpr_lift_bind hqTy.isClean hnfQ evQ) .nil))
                  (by simpa [instanceName, Instance.symbol] using spec.add_mk _ nq vnm vq vy h1' hvnm hnq hvy'))
                (matchPattern_bind_ok y vy)
                (evalExpr_lift_bind_under hrestTy.isClean hcondRest evRest)
            · split at h2
              · next hcond =>
                simp only [Option.some.injEq] at h2; subst h2
                simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
                obtain ⟨⟨⟨rfl, hnfP⟩, hatomP⟩, hcondRest⟩ := hcond
                have hpTy' := hasTy_drop_bind hpTy hnfP
                rw [Lower.letE] at ev
                obtain ⟨vy, h1', evAdd3, evRest⟩ := evalExpr_let_bind_qual_inv ev
                rw [Lower.callE, qualifyExprF_call] at evAdd3
                simp only [Option.map_some, List.map_nil, List.map_cons,
                  show qualifyName "UInt32::add3" = "UInt32::add3" from rfl] at evAdd3
                obtain ⟨vp, va, vb, hp1, ha1, hm, evP, evA, evB, hfn⟩ := evalExpr_call3_inv evAdd3
                obtain ⟨rfl, evPm⟩ := evalExpr_isPureU32Atom_heapIndep spec (h2 := hm) hatomP evP
                obtain ⟨np, hnp⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hpTy' henv evP)
                obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA)
                have hext1 := evA.heap_extends
                obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henv.mono hext1 hext1.length_le) evB)
                obtain ⟨hvy, rfl⟩ := spec.peep.add3 np na nb vp va vb hm vy h1' hnp hna hnb hfn
                let vnm := u32ValOfNat F ((na + nb) % U32.base)
                have hvnm : isU32Val ((na + nb) % U32.base) vnm := isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
                have hvy' : isU32Val ((np + (na + nb) % U32.base) % U32.base) vy := by
                  rwa [Peephole.add3_right_nat]
                rw [qualifyExprF_letValue, qualifyExprF_call, qualifyExprF_letValue, qualifyExprF_call]
                simp only [Option.map_some, List.map_nil, List.map_cons,
                  show qualifyName "UInt32::add" = "UInt32::add" from rfl]
                refine .letValue (.call (.cons evA (.cons evB .nil))
                    (by simpa [instanceName, Instance.symbol] using spec.add_mk na nb va vb vnm h1' hna hnb hvnm))
                  (matchPattern_bind_ok nm vnm) ?_
                have evVar : EvalExpr world [] ((nm, vnm) :: locals) (qualifyExprF F (Lower.vE nm)) h1' vnm h1' := by
                  rw [Lower.vE, qualifyExprF_var]; exact .var (by simp)
                refine .letValue (.call (.cons (evalExpr_lift_bind hpTy.isClean hnfP evPm) (.cons evVar .nil))
                    (by simpa [instanceName, Instance.symbol] using spec.add_mk np _ vp vnm vy h1' hnp hvnm hvy'))
                  (matchPattern_bind_ok y vy)
                  (evalExpr_lift_bind_under hrestTy.isClean hcondRest evRest)
              · cases h2
        · cases hr : Peephole.matchAdd body with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            have hbodyEq := matchAdd_eq hr; subst hbodyEq
            obtain ⟨rfl, hpTy, hqTy⟩ := hasTy_u32Bin_inv (Or.inl rfl) hb
            split at h2
            · next hcond =>
              simp only [Option.some.injEq] at h2; subst h2
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
              obtain ⟨rfl, hnfQ⟩ := hcond
              have hqTy' := hasTy_drop_bind hqTy hnfQ
              rw [Lower.callE, qualifyExprF_call] at ev
              simp only [Option.map_some, List.map_nil, List.map_cons,
                show qualifyName "UInt32::add3" = "UInt32::add3" from rfl] at ev
              obtain ⟨va, vb, vq, ha1, hb1, hm, evA, evB, evQ, hfn⟩ := evalExpr_call3_inv ev
              obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA)
              have hext1 := evA.heap_extends
              obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henv.mono hext1 hext1.length_le) evB)
              have hext2 := hext1.trans evB.heap_extends
              obtain ⟨nq, hnq⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hqTy' (henv.mono hext2 hext2.length_le) evQ)
              obtain ⟨hvr, rfl⟩ := spec.peep.add3 na nb nq va vb vq hm r h' hna hnb hnq hfn
              let vnm := u32ValOfNat F ((na + nb) % U32.base)
              have hvnm : isU32Val ((na + nb) % U32.base) vnm := isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
              have hvr' : isU32Val (((na + nb) % U32.base + nq) % U32.base) r := by
                rwa [Peephole.add3_left_nat]
              rw [qualifyExprF_letValue, qualifyExprF_call, qualifyExprF_call]
              simp only [Option.map_some, List.map_nil, List.map_cons,
                show qualifyName "UInt32::add" = "UInt32::add" from rfl]
              refine .letValue (.call (.cons evA (.cons evB .nil))
                  (by simpa [instanceName, Instance.symbol] using spec.add_mk na nb va vb vnm hb1 hna hnb hvnm))
                (matchPattern_bind_ok nm vnm) ?_
              have evVar : EvalExpr world [] ((nm, vnm) :: locals) (qualifyExprF F (Lower.vE nm)) hb1 vnm hb1 := by
                rw [Lower.vE, qualifyExprF_var]; exact .var (by simp)
              exact .call (.cons evVar (.cons (evalExpr_lift_bind hqTy.isClean hnfQ evQ) .nil))
                (by simpa [instanceName, Instance.symbol] using spec.add_mk _ nq vnm vq r h' hvnm hnq hvr')
            · split at h2
              · next hcond =>
                simp only [Option.some.injEq] at h2; subst h2
                simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
                obtain ⟨⟨rfl, hnfP⟩, hatomP⟩ := hcond
                have hpTy' := hasTy_drop_bind hpTy hnfP
                rw [Lower.callE, qualifyExprF_call] at ev
                simp only [Option.map_some, List.map_nil, List.map_cons,
                  show qualifyName "UInt32::add3" = "UInt32::add3" from rfl] at ev
                obtain ⟨vp, va, vb, hp1, ha1, hm, evP, evA, evB, hfn⟩ := evalExpr_call3_inv ev
                obtain ⟨rfl, evPm⟩ := evalExpr_isPureU32Atom_heapIndep spec (h2 := hm) hatomP evP
                obtain ⟨np, hnp⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hpTy' henv evP)
                obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henv evA)
                have hext1 := evA.heap_extends
                obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henv.mono hext1 hext1.length_le) evB)
                obtain ⟨hvr, rfl⟩ := spec.peep.add3 np na nb vp va vb hm r h' hnp hna hnb hfn
                let vnm := u32ValOfNat F ((na + nb) % U32.base)
                have hvnm : isU32Val ((na + nb) % U32.base) vnm := isU32Val_u32ValOfNat (Nat.mod_lt _ (by decide))
                have hvr' : isU32Val ((np + (na + nb) % U32.base) % U32.base) r := by
                  rwa [Peephole.add3_right_nat]
                rw [qualifyExprF_letValue, qualifyExprF_call, qualifyExprF_call]
                simp only [Option.map_some, List.map_nil, List.map_cons,
                  show qualifyName "UInt32::add" = "UInt32::add" from rfl]
                refine .letValue (.call (.cons evA (.cons evB .nil))
                    (by simpa [instanceName, Instance.symbol] using spec.add_mk na nb va vb vnm h' hna hnb hvnm))
                  (matchPattern_bind_ok nm vnm) ?_
                have evVar : EvalExpr world [] ((nm, vnm) :: locals) (qualifyExprF F (Lower.vE nm)) h' vnm h' := by
                  rw [Lower.vE, qualifyExprF_var]; exact .var (by simp)
                exact .call (.cons (evalExpr_lift_bind hpTy.isClean hnfP evPm) (.cons evVar .nil))
                  (by simpa [instanceName, Instance.symbol] using spec.add_mk np _ vp vnm r h' hnp hvnm hvr')
              · cases h2
    | none =>
      rw [h2] at htr
      cases h3 : Peephole.tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at htr; simp only [Option.some.injEq] at htr; subst htr
        unfold Peephole.tryFuseLetRotr at h3
        cases hs1 : Peephole.matchShiftConst env val with
        | none => simp [hs1] at h3
        | some t1 =>
          rcases t1 with ⟨d1, x1, k1⟩; rw [hs1] at h3; dsimp only at h3
          obtain ⟨rfl, hx1Ty⟩ := hasTy_shift_inv hSigs hs1 hv
          split at h3
          · cases h3
          · next hpX1 =>
            have hpX1' : Peephole.isHeapPure x1 = true := by
              cases h : Peephole.isHeapPure x1 <;> simp_all
            split at h3
            · next s2 val2 body2 =>
              simp only [literalsBounded, Bool.and_eq_true] at hlbB
              cases hb with | letValue hval2Ty hpS2 hbody2Ty =>
              cases hpS2
              split at h3
              · cases h3
              · next hs2Ne =>
                have hs2Ne' : s2 ≠ nm := fun heq => hs2Ne (by simp [heq])
                cases hs2 : Peephole.matchShiftConst env val2 with
                | none => simp [hs2] at h3
                | some t2 =>
                  rcases t2 with ⟨d2, x2, k2⟩; rw [hs2] at h3; dsimp only at h3
                  obtain ⟨rfl, hx2Ty⟩ := hasTy_shift_inv hSigs hs2 hval2Ty
                  split at h3
                  · cases h3
                  · next hchk =>
                    have hdNe : d1 ≠ d2 := fun heq => hchk (by simp [heq])
                    have hxEq : x1 = x2 := by
                      by_contra hneq; apply hchk; simp [beq_false_of_ne hneq]
                    have hnfX2 : Peephole.occursFree nm x2 = false := by
                      cases h : Peephole.occursFree nm x2
                      · rfl
                      · exact False.elim (hchk (by simp [h]))
                    subst hxEq
                    cases hrot : Peephole.rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                    | none => simp [hrot] at h3
                    | some rnm =>
                      rw [hrot] at h3; dsimp only at h3
                      have buildOr : ∀ {o1 o2 : Expr} {vy : SourceValue F} {hh : Heap F},
                          Peephole.isVarPair nm s2 o1 o2 = true →
                          EvalExpr world [] locals (qualifyExprF F (Lower.callE rnm [x1])) hh vy hh →
                          EnvOk enums hh hh.length Γ locals →
                          ∃ v1 v2,
                            EvalExpr world [] locals (qualifyExprF F val) hh v1 hh ∧
                            EvalExpr world [] ((nm, v1) :: locals) (qualifyExprF F val2) hh v2 hh ∧
                            EvalExpr world [] ((s2, v2) :: (nm, v1) :: locals)
                              (qualifyExprF F (.call "UInt32::or" (some []) [o1, o2])) hh vy hh := by
                        intro o1 o2 vy hh hvp evRot henvH
                        rw [Lower.callE, qualifyExprF_call] at evRot
                        simp only [Option.map_some, List.map_nil, List.map_cons] at evRot
                        obtain ⟨vx, hm, evX, hfnRot⟩ := evalExpr_call1_inv evRot
                        have hhh := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hpX1' hx1Ty henvH evX
                        subst hhh
                        obtain ⟨nx, hnx⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hx1Ty henvH evX)
                        have hvyRot : isU32Val ((nx >>> (if d1 = true then k1 else k2)) |||
                            ((nx <<< (if d1 = true then k2 else k1)) % U32.base)) vy := by
                          rcases rotrFnOf?_inv hrot with ⟨hk1, hk2, rfl⟩ | ⟨hk1, hk2, rfl⟩
                          · obtain ⟨hru, _⟩ := spec.peep.rotr16 nx vx hm vy hm hnx hfnRot
                            rwa [hk1, hk2]
                          · obtain ⟨hru, _⟩ := spec.peep.rotr8 nx vx hm vy hm hnx hfnRot
                            rwa [hk1, hk2]
                        obtain ⟨v1, ev1, hv1⟩ := evalExpr_shift_mk spec hSigs hs1 hlbV hv hce evX hnx
                        have evX' := evalExpr_lift_bind (v := v1) hx1Ty.isClean hnfX2 evX
                        have hce1 := constEnvOk_cons_not_mem (val := v1) (tv := u32Ty) hce hnotNm
                        obtain ⟨v2, ev2, hv2⟩ := evalExpr_shift_mk spec hSigs hs2 hlbB.1 hval2Ty hce1 evX' hnx
                        refine ⟨v1, v2, ev1, ev2, ?_⟩
                        rw [qualifyExprF_call]
                        simp only [Option.map_some, List.map_nil, List.map_cons,
                          show qualifyName "UInt32::or" = "UInt32::or" from rfl]
                        have hvar1 : EvalExpr world [] ((s2, v2) :: (nm, v1) :: locals) (.var nm) hm v1 hm :=
                          .var (by simp [beq_false_of_ne hs2Ne'])
                        have hvar2 : EvalExpr world [] ((s2, v2) :: (nm, v1) :: locals) (.var s2) hm v2 hm :=
                          .var (by simp)
                        cases d1 <;> cases d2
                        · exact absurd rfl hdNe
                        · simp only [Bool.false_eq_true, ↓reduceIte] at hv1 hv2 hvyRot
                          rcases isVarPair_inv hvp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar1)
                                (.cons (by rw [qualifyExprF_var]; exact hvar2) .nil))
                              (by simpa [instanceName, Instance.symbol] using
                                spec.or_mk _ _ v1 v2 vy hm hv1 hv2 (by rwa [nat_lor_comm]))
                          · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar2)
                                (.cons (by rw [qualifyExprF_var]; exact hvar1) .nil))
                              (by simpa [instanceName, Instance.symbol] using
                                spec.or_mk _ _ v2 v1 vy hm hv2 hv1 hvyRot)
                        · simp only [↓reduceIte, Bool.false_eq_true] at hv1 hv2 hvyRot
                          rcases isVarPair_inv hvp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar1)
                                (.cons (by rw [qualifyExprF_var]; exact hvar2) .nil))
                              (by simpa [instanceName, Instance.symbol] using
                                spec.or_mk _ _ v1 v2 vy hm hv1 hv2 hvyRot)
                          · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar2)
                                (.cons (by rw [qualifyExprF_var]; exact hvar1) .nil))
                              (by simpa [instanceName, Instance.symbol] using
                                spec.or_mk _ _ v2 v1 vy hm hv2 hv1 (by rwa [nat_lor_comm]))
                        · exact absurd rfl hdNe
                      have rotPure : ∀ {vy : SourceValue F} {hh hh' : Heap F},
                          EvalExpr world [] locals (qualifyExprF F (Lower.callE rnm [x1])) hh vy hh' →
                          EnvOk enums hh hh.length Γ locals → hh' = hh := by
                        intro vy hh hh' evRot henvH
                        rw [Lower.callE, qualifyExprF_call] at evRot
                        simp only [Option.map_some, List.map_nil, List.map_cons] at evRot
                        obtain ⟨vx, hm, evX, hfnRot⟩ := evalExpr_call1_inv evRot
                        have hhh := evalExpr_isHeapPure hnd hHas hProv hLib spec hWT hSigs hpX1' hx1Ty henvH evX
                        subst hhh
                        obtain ⟨nx, hnx⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hx1Ty henvH evX)
                        rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
                        · exact (spec.peep.rotr16 nx vx hm vy hh' hnx hfnRot).2
                        · exact (spec.peep.rotr8 nx vx hm vy hh' hnx hfnRot).2
                      split at h3
                      · next y rhs rest =>
                        cases hbody2Ty with | letValue hrhsTy hpY hrestTy =>
                        cases hpY
                        cases hor : Peephole.matchOr rhs with
                        | none => simp [hor] at h3
                        | some po =>
                          rcases po with ⟨o1, o2⟩; rw [hor] at h3; dsimp only at h3
                          have hrhsEq := matchOr_eq hor; subst hrhsEq
                          split at h3
                          · next hcond =>
                            simp only [Option.some.injEq] at h3; subst h3
                            simp only [Bool.and_eq_true] at hcond
                            obtain ⟨⟨hvp, hcondNm⟩, hcondS2⟩ := hcond
                            rw [Lower.letE] at ev
                            obtain ⟨vy, h1', evRot, evRest⟩ := evalExpr_let_bind_qual_inv ev
                            have hh1 := rotPure evRot henv; subst hh1
                            obtain ⟨v1, v2, ev1, ev2, evOr⟩ := buildOr hvp evRot henv
                            have evRest1 := evalExpr_lift_bind_under (v := v1) hrestTy.isClean hcondNm evRest
                            have evRest2 := evalExpr_lift_bind_under (v := v2) hrestTy.isClean hcondS2 evRest1
                            rw [qualifyExprF_letValue, qualifyExprF_letValue, qualifyExprF_letValue]
                            exact .letValue ev1 (matchPattern_bind_ok nm v1)
                              (.letValue ev2 (matchPattern_bind_ok s2 v2)
                                (.letValue evOr (matchPattern_bind_ok y vy) evRest2))
                          · cases h3
                      · cases hor : Peephole.matchOr body2 with
                        | none => simp [hor] at h3
                        | some po =>
                          rcases po with ⟨o1, o2⟩; rw [hor] at h3; dsimp only at h3
                          have hbody2Eq := matchOr_eq hor; subst hbody2Eq
                          split at h3
                          · next hvp =>
                            simp only [Option.some.injEq] at h3; subst h3
                            have hh1 := rotPure ev henv; subst hh1
                            obtain ⟨v1, v2, ev1, ev2, evOr⟩ := buildOr hvp ev henv
                            rw [qualifyExprF_letValue, qualifyExprF_letValue]
                            exact .letValue ev1 (matchPattern_bind_ok nm v1)
                              (.letValue ev2 (matchPattern_bind_ok s2 v2) evOr)
                          · cases h3
            · cases h3
      | none =>
        rw [h3] at htr
        cases h4 : Peephole.tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at htr; simp only [Option.some.injEq] at htr; subst htr
          unfold Peephole.tryFuseLetXorRotr4 at h4; split at h4
          · next a b s1 val1 s2 val2 body2 hx =>
            have hvalEq := matchXor_eq hx; subst hvalEq
            obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inr (Or.inl rfl)) hv
            simp only [literalsBounded, Bool.and_eq_true] at hlbB
            cases hb with | letValue hval1Ty hpS1 hinner =>
            cases hpS1
            cases hinner with | letValue hval2Ty hpS2 hbody2Ty =>
            cases hpS2
            have hnotS1 : s1 ∉ env.map Prod.fst :=
              hnotB s1 (by simp [hasBoundVar, patBoundVars])
            split at h4
            · cases h4
            · next hne =>
              have hs1Nm : s1 ≠ nm := fun heq => hne (by simp [heq])
              have hs2Nm : s2 ≠ nm := fun heq => hne (by simp [heq])
              have hs1S2 : s1 ≠ s2 := fun heq => hne (by simp [heq])
              split at h4
              · next d1 x1 k1 d2 x2 k2 hs1 hs2 =>
                obtain ⟨rfl, _⟩ := hasTy_shift_inv hSigs hs1 hval1Ty
                obtain ⟨rfl, _⟩ := hasTy_shift_inv hSigs hs2 hval2Ty
                split at h4
                · cases h4
                · next hchk =>
                  have hdNe : d1 ≠ d2 := fun heq => hchk (by simp [heq])
                  have hx1Eq : x1 = .var nm := by
                    by_contra hneq; apply hchk; simp [Lower.vE, beq_false_of_ne hneq]
                  have hx2Eq : x2 = .var nm := by
                    by_contra hneq; apply hchk; simp [Lower.vE, beq_false_of_ne hneq]
                  subst hx1Eq; subst hx2Eq
                  dsimp only at h4
                  cases hxr : Peephole.xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                  | none => simp [hxr] at h4
                  | some xfn =>
                    rw [hxr] at h4; dsimp only at h4
                    have buildChain : ∀ {o1 o2 : Expr} {vy : SourceValue F} {hh hm : Heap F},
                        Peephole.isVarPair s1 s2 o1 o2 = true →
                        EvalExpr world [] locals (qualifyExprF F (Lower.callE xfn [a, b])) hh vy hm →
                        EnvOk enums hh hh.length Γ locals →
                        ∃ vxor vs1 vs2,
                          EvalExpr world [] locals (qualifyExprF F (.call "UInt32::xor" (some []) [a, b])) hh vxor hm ∧
                          EvalExpr world [] ((nm, vxor) :: locals) (qualifyExprF F val1) hm vs1 hm ∧
                          EvalExpr world [] ((s1, vs1) :: (nm, vxor) :: locals) (qualifyExprF F val2) hm vs2 hm ∧
                          EvalExpr world [] ((s2, vs2) :: (s1, vs1) :: (nm, vxor) :: locals)
                            (qualifyExprF F (.call "UInt32::or" (some []) [o1, o2])) hm vy hm := by
                      intro o1 o2 vy hh hm hvp evXr henvH
                      rw [Lower.callE, qualifyExprF_call] at evXr
                      simp only [Option.map_some, List.map_nil, List.map_cons] at evXr
                      obtain ⟨va, vb, h1', h2', evA, evB, hfnXr⟩ := evalExpr_call2_inv evXr
                      obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henvH evA)
                      have hext1 := evA.heap_extends
                      obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henvH.mono hext1 hext1.length_le) evB)
                      have hvyRot : isU32Val ((Nat.xor na nb >>> (if d1 = true then k1 else k2)) |||
                          ((Nat.xor na nb <<< (if d1 = true then k2 else k1)) % U32.base)) vy ∧ hm = h2' := by
                        rcases xorRotrFnOf?_inv hxr with ⟨hk1, hk2, rfl⟩ | ⟨hk1, hk2, rfl⟩
                        · obtain ⟨hru, heq⟩ := spec.peep.xor_rotr12 na nb va vb h2' vy hm hna hnb hfnXr
                          rw [hk1, hk2]; exact ⟨hru, heq⟩
                        · obtain ⟨hru, heq⟩ := spec.peep.xor_rotr7 na nb va vb h2' vy hm hna hnb hfnXr
                          rw [hk1, hk2]; exact ⟨hru, heq⟩
                      obtain ⟨hvyRot, rfl⟩ := hvyRot
                      let vxor := u32ValOfNat F (Nat.xor na nb)
                      have hvxor : isU32Val (Nat.xor na nb) vxor :=
                        isU32Val_u32ValOfNat (Nat.xor_lt_two_pow (n := 32) (isU32Val_lt hna) (isU32Val_lt hnb))
                      have evXor : EvalExpr world [] locals (qualifyExprF F (.call "UInt32::xor" (some []) [a, b])) hh vxor hm := by
                        rw [qualifyExprF_call]
                        simp only [Option.map_some, List.map_nil, List.map_cons,
                          show qualifyName "UInt32::xor" = "UInt32::xor" from rfl]
                        exact .call (.cons evA (.cons evB .nil))
                          (by simpa [instanceName, Instance.symbol] using spec.xor_mk na nb va vb vxor hm hna hnb hvxor)
                      have hce1 := constEnvOk_cons_not_mem (val := vxor) (tv := u32Ty) hce hnotNm
                      have evNm1 : EvalExpr world [] ((nm, vxor) :: locals) (qualifyExprF F (.var nm)) hm vxor hm := by
                        rw [qualifyExprF_var]; exact .var (by simp)
                      obtain ⟨vs1, evS1, hvs1⟩ := evalExpr_shift_mk spec hSigs hs1 hlbB.1 hval1Ty hce1 evNm1 hvxor
                      have hce2 := constEnvOk_cons_not_mem (val := vs1) (tv := u32Ty) hce1 hnotS1
                      have evNm2 : EvalExpr world [] ((s1, vs1) :: (nm, vxor) :: locals) (qualifyExprF F (.var nm)) hm vxor hm := by
                        rw [qualifyExprF_var]; exact .var (by simp [beq_false_of_ne hs1Nm])
                      obtain ⟨vs2, evS2, hvs2⟩ := evalExpr_shift_mk spec hSigs hs2 hlbB.2.1 hval2Ty hce2 evNm2 hvxor
                      refine ⟨vxor, vs1, vs2, evXor, evS1, evS2, ?_⟩
                      rw [qualifyExprF_call]
                      simp only [Option.map_some, List.map_nil, List.map_cons,
                        show qualifyName "UInt32::or" = "UInt32::or" from rfl]
                      have hvar1 : EvalExpr world [] ((s2, vs2) :: (s1, vs1) :: (nm, vxor) :: locals) (.var s1) hm vs1 hm :=
                        .var (by simp [beq_false_of_ne (Ne.symm hs1S2)])
                      have hvar2 : EvalExpr world [] ((s2, vs2) :: (s1, vs1) :: (nm, vxor) :: locals) (.var s2) hm vs2 hm :=
                        .var (by simp)
                      cases d1 <;> cases d2
                      · exact absurd rfl hdNe
                      · simp only [Bool.false_eq_true, ↓reduceIte] at hvs1 hvs2 hvyRot
                        rcases isVarPair_inv hvp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar1)
                              (.cons (by rw [qualifyExprF_var]; exact hvar2) .nil))
                            (by simpa [instanceName, Instance.symbol] using
                              spec.or_mk _ _ vs1 vs2 vy hm hvs1 hvs2 (by rwa [nat_lor_comm]))
                        · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar2)
                              (.cons (by rw [qualifyExprF_var]; exact hvar1) .nil))
                            (by simpa [instanceName, Instance.symbol] using
                              spec.or_mk _ _ vs2 vs1 vy hm hvs2 hvs1 hvyRot)
                      · simp only [↓reduceIte, Bool.false_eq_true] at hvs1 hvs2 hvyRot
                        rcases isVarPair_inv hvp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar1)
                              (.cons (by rw [qualifyExprF_var]; exact hvar2) .nil))
                            (by simpa [instanceName, Instance.symbol] using
                              spec.or_mk _ _ vs1 vs2 vy hm hvs1 hvs2 hvyRot)
                        · exact .call (.cons (by rw [qualifyExprF_var]; exact hvar2)
                              (.cons (by rw [qualifyExprF_var]; exact hvar1) .nil))
                            (by simpa [instanceName, Instance.symbol] using
                              spec.or_mk _ _ vs2 vs1 vy hm hvs2 hvs1 (by rwa [nat_lor_comm]))
                      · exact absurd rfl hdNe
                    split at h4
                    · next y rhs rest =>
                      cases hbody2Ty with | letValue hrhsTy hpY hrestTy =>
                      cases hpY
                      cases hor : Peephole.matchOr rhs with
                      | none => simp [hor] at h4
                      | some po =>
                        rcases po with ⟨o1, o2⟩; rw [hor] at h4; dsimp only at h4
                        have hrhsEq := matchOr_eq hor; subst hrhsEq
                        split at h4
                        · next hcond =>
                          simp only [Option.some.injEq] at h4; subst h4
                          simp only [Bool.and_eq_true] at hcond
                          obtain ⟨⟨⟨hvp, hcondNm⟩, hcondS1⟩, hcondS2⟩ := hcond
                          rw [Lower.letE] at ev
                          obtain ⟨vy, hm, evXr, evRest⟩ := evalExpr_let_bind_qual_inv ev
                          obtain ⟨vxor, vs1, vs2, evXor, evS1, evS2, evOr⟩ := buildChain hvp evXr henv
                          have evR1 := evalExpr_lift_bind_under (v := vxor) hrestTy.isClean hcondNm evRest
                          have evR2 := evalExpr_lift_bind_under (v := vs1) hrestTy.isClean hcondS1 evR1
                          have evR3 := evalExpr_lift_bind_under (v := vs2) hrestTy.isClean hcondS2 evR2
                          rw [qualifyExprF_letValue, qualifyExprF_letValue, qualifyExprF_letValue, qualifyExprF_letValue]
                          exact .letValue evXor (matchPattern_bind_ok nm vxor)
                            (.letValue evS1 (matchPattern_bind_ok s1 vs1)
                              (.letValue evS2 (matchPattern_bind_ok s2 vs2)
                                (.letValue evOr (matchPattern_bind_ok y vy) evR3)))
                        · cases h4
                    · cases hor : Peephole.matchOr body2 with
                      | none => simp [hor] at h4
                      | some po =>
                        rcases po with ⟨o1, o2⟩; rw [hor] at h4; dsimp only at h4
                        have hbody2Eq := matchOr_eq hor; subst hbody2Eq
                        split at h4
                        · next hvp =>
                          simp only [Option.some.injEq] at h4; subst h4
                          obtain ⟨vxor, vs1, vs2, evXor, evS1, evS2, evOr⟩ := buildChain hvp ev henv
                          rw [qualifyExprF_letValue, qualifyExprF_letValue, qualifyExprF_letValue]
                          exact .letValue evXor (matchPattern_bind_ok nm vxor)
                            (.letValue evS1 (matchPattern_bind_ok s1 vs1)
                              (.letValue evS2 (matchPattern_bind_ok s2 vs2) evOr))
                        · cases h4
              · cases h4
          · cases h4
        | none =>
          rw [h4] at htr
          unfold Peephole.tryFuseLetXorRotrHalf at htr
          cases hx : Peephole.matchXor val with
          | none => simp [hx] at htr
          | some pab =>
            rcases pab with ⟨a, b⟩; rw [hx] at htr; dsimp only at htr
            have hvalEq := matchXor_eq hx; subst hvalEq
            obtain ⟨rfl, haTy, hbTy⟩ := hasTy_u32Bin_inv (Or.inr (Or.inl rfl)) hv
            have buildHalf : ∀ {e1 e2 : Expr} {kShr kShl : Nat} {xfn : String}
                {vy : SourceValue F} {hh hm : Heap F},
                Peephole.matchRotPair env e1 e2 = some (.var nm, kShr, kShl) →
                Peephole.xorRotrFnOf? kShr kShl = some xfn →
                literalsBounded e1 = true → literalsBounded e2 = true →
                HasTy (sigsWithU32OfField (fnSigsOf fns)) enums ((nm, u32Ty) :: Γ) e1 u32Ty →
                HasTy (sigsWithU32OfField (fnSigsOf fns)) enums ((nm, u32Ty) :: Γ) e2 u32Ty →
                EvalExpr world [] locals (qualifyExprF F (Lower.callE xfn [a, b])) hh vy hm →
                EnvOk enums hh hh.length Γ locals →
                ∃ vxor,
                  EvalExpr world [] locals (qualifyExprF F (.call "UInt32::xor" (some []) [a, b])) hh vxor hm ∧
                  EvalExpr world [] ((nm, vxor) :: locals)
                    (qualifyExprF F (.call "UInt32::or" (some []) [e1, e2])) hm vy hm := by
              intro e1 e2 kShr kShl xfn vy hh hm hrp hxr hlb1 hlb2 hty1 hty2 evXr henvH
              rw [Lower.callE, qualifyExprF_call] at evXr
              simp only [Option.map_some, List.map_nil, List.map_cons] at evXr
              obtain ⟨va, vb, h1', h2', evA, evB, hfnXr⟩ := evalExpr_call2_inv evXr
              obtain ⟨na, hna⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT haTy henvH evA)
              have hext1 := evA.heap_extends
              obtain ⟨nb, hnb⟩ := (ValOk_u32 ..).mp (evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hbTy (henvH.mono hext1 hext1.length_le) evB)
              have hvyRot : isU32Val ((Nat.xor na nb >>> kShr) ||| ((Nat.xor na nb <<< kShl) % U32.base)) vy ∧ hm = h2' := by
                rcases xorRotrFnOf?_inv hxr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                · exact spec.peep.xor_rotr12 na nb va vb h2' vy hm hna hnb hfnXr
                · exact spec.peep.xor_rotr7 na nb va vb h2' vy hm hna hnb hfnXr
              obtain ⟨hvyRot, rfl⟩ := hvyRot
              let vxor := u32ValOfNat F (Nat.xor na nb)
              have hvxor : isU32Val (Nat.xor na nb) vxor :=
                isU32Val_u32ValOfNat (Nat.xor_lt_two_pow (n := 32) (isU32Val_lt hna) (isU32Val_lt hnb))
              have evXor : EvalExpr world [] locals (qualifyExprF F (.call "UInt32::xor" (some []) [a, b])) hh vxor hm := by
                rw [qualifyExprF_call]
                simp only [Option.map_some, List.map_nil, List.map_cons,
                  show qualifyName "UInt32::xor" = "UInt32::xor" from rfl]
                exact .call (.cons evA (.cons evB .nil))
                  (by simpa [instanceName, Instance.symbol] using spec.xor_mk na nb va vb vxor hm hna hnb hvxor)
              have hce1 := constEnvOk_cons_not_mem (val := vxor) (tv := u32Ty) hce hnotNm
              have evNm : EvalExpr world [] ((nm, vxor) :: locals) (qualifyExprF F (.var nm)) hm vxor hm := by
                rw [qualifyExprF_var]; exact .var (by simp)
              exact ⟨vxor, evXor, evalExpr_rotPair_mk spec hSigs hrp hlb1 hlb2 hty1 hty2 hce1 evNm hvxor hvyRot⟩
            split at htr
            · next y rhs rest =>
              simp only [literalsBounded, Bool.and_eq_true] at hlbB
              cases hb with | letValue hrhsTy hpY hrestTy =>
              cases hpY
              cases hor : Peephole.matchOr rhs with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                have hrhsEq := matchOr_eq hor; subst hrhsEq
                obtain ⟨rfl, hty1, hty2⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hrhsTy
                have hlbRhs := literalsBounded_call_args hlbB.1
                simp only [literalsBoundedList, Bool.and_eq_true] at hlbRhs
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨x, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr
                  split at htr
                  · cases htr
                  · next hnot =>
                    have hxEq : x = .var nm := by
                      by_contra hneq; apply hnot; simp [Lower.vE, beq_false_of_ne hneq]
                    subst hxEq
                    have hcondNm : (nm == y || !Peephole.occursFree nm rest) = true := by
                      by_contra hf; apply hnot; simp [Bool.eq_false_iff.mpr hf]
                    cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rw [Lower.letE] at ev
                      obtain ⟨vy, hm, evXr, evRest⟩ := evalExpr_let_bind_qual_inv ev
                      obtain ⟨vxor, evXor, evOr⟩ :=
                        buildHalf hrp hxr hlbRhs.1 hlbRhs.2.1 hty1 hty2 evXr henv
                      rw [qualifyExprF_letValue, qualifyExprF_letValue]
                      exact .letValue evXor (matchPattern_bind_ok nm vxor)
                        (.letValue evOr (matchPattern_bind_ok y vy)
                          (evalExpr_lift_bind_under hrestTy.isClean hcondNm evRest))
            · cases hor : Peephole.matchOr body with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                have hbodyEq := matchOr_eq hor; subst hbodyEq
                obtain ⟨rfl, hty1, hty2⟩ := hasTy_u32Bin_inv (Or.inr (Or.inr rfl)) hb
                have hlbOr := literalsBounded_call_args hlbB
                simp only [literalsBoundedList, Bool.and_eq_true] at hlbOr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨x, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr
                  split at htr
                  · cases htr
                  · next hnot =>
                    have hxEq : x = .var nm := by
                      by_contra hneq; apply hnot; simp [Lower.vE, beq_false_of_ne hneq]
                    subst hxEq
                    cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      obtain ⟨vxor, evXor, evOr⟩ :=
                        buildHalf hrp hxr hlbOr.1 hlbOr.2.1 hty1 hty2 ev henv
                      rw [qualifyExprF_letValue]
                      exact .letValue evXor (matchPattern_bind_ok nm vxor) evOr

private theorem fuseArms_eq_map (env : Peephole.ConstEnv) (arms : List (Pat × Expr)) :
    Peephole.fuseArms env arms =
      arms.map fun arm => (arm.1, Peephole.fuseExpr (Peephole.envRemove (Peephole.patBoundNames arm.1) env) arm.2) := by
  induction arms with
  | nil => rfl
  | cons hd tl ih => rcases hd with ⟨p, b⟩; simp [Peephole.fuseArms, ih]

mutual

/-- **Phase 1 (`Peephole.fuseExpr`) Backward Soundness!** -/
theorem evalExpr_fuseExpr_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {scope : List String} {Γ : TyEnv} {locals : Environment F Nat}
      {e : Expr} {t : Lower.Ty} {h h' : Heap F} {r : SourceValue F},
      literalsBounded e = true →
      NoLetShadow scope e →
      (∀ k ∈ env.map Prod.fst, k ∈ scope) →
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t →
      EnvOk enums h h.length Γ locals →
      ConstEnvOk env locals Γ →
      EvalExpr world [] locals (qualifyExprF F (Peephole.fuseExpr env e)) h r h' →
      EvalExpr world [] locals (qualifyExprF F e) h r h'
  | _, _, _, _, _, _, _, _, _, _, _, _, .literal, _, _, ev => ev
  | _, _, _, _, _, _, _, _, _, _, _, _, .var _, _, _, ev => ev
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .tuple items, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple evs =>
      exact .tuple (evalArgs_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub items henv hce evs)
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .array _ items, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array evs =>
      exact .array (evalArgs_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub items henv hce evs)
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .repeat hx, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item =>
      exact .repeat (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item)
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .index hx, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp =>
      exact .index (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item) hp
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .project hx _, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp =>
      exact .project (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item) hp
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .slice _ hx, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs =>
      exact .slice (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item) hs
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .construct _ _ _ _ _ items, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct evs =>
      exact .construct (evalArgs_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub items henv hce evs)
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .builtin items, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin evs ha =>
      exact .builtin (evalArgs_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub items henv hce evs) ha
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .store hx, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item =>
      exact .store (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item)
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .load hx, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl =>
      exact .load (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item) hl
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .hint _ hx, henv, hce, ev => by
    simp only [literalsBounded] at hlb
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht =>
      exact .hint (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item) ht
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .neg hx, henv, hce, ev => by
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop =>
      exact .neg (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb hns hsub hx henv hce item) hop
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .binary hl hr, henv, hce, ev => by
    simp only [literalsBounded, Bool.and_eq_true] at hlb
    rcases hns with ⟨_, hnsL, hnsR⟩
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | binary evL evR hop =>
      have evL' := evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hnsL hsub hl henv hce evL
      have hext := evL'.heap_extends
      have evR' := evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.2 hnsR hsub hr
        (henv.mono hext hext.length_le) hce evR
      exact .binary evL' evR' hop
  | env, _, Γ, locals, .call nm (some []) xs, t, h, h', r, hlb, hns, hsub, .call hsig items, henv, hce, ev => by
    simp only [Peephole.fuseExpr] at ev
    have hlbXs := literalsBounded_call_args hlb
    have hlbXs' := literalsBounded_fuseList env hlbXs
    have htyCall' : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ
        (.call nm (some []) (Peephole.fuseList env xs)) t :=
      .call hsig (hasTy_fuseList hSigs env items)
    have evCall' : EvalExpr world [] locals
        (qualifyExprF F (.call nm (some []) (Peephole.fuseList env xs))) h r h' := by
      cases htr : Peephole.tryFuseCall env nm (some []) (Peephole.fuseList env xs) with
      | none => simpa [htr] using ev
      | some e' =>
        rw [htr, Option.getD_some] at ev
        exact evalExpr_tryFuseCall_backward hnd hHas hProv hLib spec hWT hSigs
          htr hlbXs' htyCall' henv hce ev
    rw [qualifyExprF_call] at evCall' ⊢
    cases evCall' with | call evArgs hfn =>
      exact .call
        (evalArgs_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlbXs hns hsub items henv hce evArgs) hfn
  | env, scope, Γ, locals, .letValue p v b, tb, h, h', r, hlb, hns, hsub,
      .letValue (tx := tv) (Δ := Δ) hv hp hb, henv, hce, ev => by
    simp only [literalsBounded, Bool.and_eq_true] at hlb
    rcases hns with ⟨hnp, _, hnsV, hnsB⟩
    cases p with
    | bind nm =>
      cases hp
      simp only [Peephole.fuseExpr] at ev
      let v' := Peephole.fuseExpr env v
      let env' : Peephole.ConstEnv :=
        match Peephole.extractU32Const? env v' with
        | some k => (nm, k) :: Peephole.envRemove [nm] env
        | none => Peephole.envRemove [nm] env
      let b' := Peephole.fuseExpr env' b
      have hlbV' : literalsBounded v' = true := literalsBounded_fuseExpr env hlb.1
      have hlbB' : literalsBounded b' = true := literalsBounded_fuseExpr env' hlb.2
      have hv' : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ v' tv := hasTy_fuseExpr hSigs env hv
      have hb' : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums ((nm, tv) :: Γ) b' tb := hasTy_fuseExpr hSigs env' hb
      have hnotNm : nm ∉ env.map Prod.fst := fun hmem => hnp nm (by simp [patBoundVars]) (hsub nm hmem)
      have hnotB' : ∀ s, hasBoundVar s b' = true → s ∉ env.map Prod.fst := by
        intro s hs hmem
        have hsB := hasBoundVar_fuseExpr_sub s env' b hs
        have hfalse := noLetShadow_implies_noBoundVar hnsB s (List.mem_append_right _ (hsub s hmem))
        rw [hfalse] at hsB; cases hsB
      have evLet' : EvalExpr world [] locals (qualifyExprF F (.letValue (.bind nm) v' b')) h r h' := by
        cases htr : Peephole.tryFuseLet env nm v' b' with
        | none =>
          change EvalExpr world [] locals (qualifyExprF F ((Peephole.tryFuseLet env nm v' b').getD (.letValue (.bind nm) v' b'))) h r h' at ev
          simpa [htr] using ev
        | some e' =>
          change EvalExpr world [] locals (qualifyExprF F ((Peephole.tryFuseLet env nm v' b').getD (.letValue (.bind nm) v' b'))) h r h' at ev
          rw [htr, Option.getD_some] at ev
          exact evalExpr_tryFuseLet_backward hnd hHas hProv hLib spec hWT hSigs
            htr hlbV' hlbB' hv' hb' henv hce hnotNm hnotB' ev
      rw [qualifyExprF_letValue] at evLet' ⊢
      cases evLet' with | letValue evV' hm evB' =>
        rename_i inp _ _
        have evV := evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hnsV hsub hv henv hce evV'
        have hokV := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hv henv evV
        have hext := evV.heap_extends
        have hbs := patHasTy_matchPattern .bind hokV hm
        have henvB := envOk_append hbs (henv.mono hext hext.length_le)
        simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at hm
        subst hm
        have hsub' : ∀ k ∈ env'.map Prod.fst, k ∈ patBoundVars (.bind nm) ++ scope := by
          intro k hk
          dsimp only [env'] at hk
          cases hcext : Peephole.extractU32Const? env v' with
          | none =>
            rw [hcext] at hk; exact List.mem_append_right _ (hsub k (envRemove_subset hk))
          | some _ =>
            rw [hcext] at hk
            rcases List.mem_cons.mp hk with rfl | htl
            · exact List.mem_append_left _ (by simp [patBoundVars])
            · exact List.mem_append_right _ (hsub k (envRemove_subset htl))
        have hceB : ConstEnvOk env' ([(nm, inp)] ++ locals) ([(nm, tv)] ++ Γ) := by
          dsimp only [env']
          cases hcext : Peephole.extractU32Const? env v' with
          | none => exact constEnvOk_envRemove (by simp) (by simp) hce
          | some k =>
            refine constEnvOk_cons_val hce fun htv => ?_
            subst htv
            exact (evalExpr_extractU32Const?_sound spec hcext hlbV' hv' hce evV').1
        exact .letValue evV (matchPattern_bind_ok nm inp)
          (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env' hlb.2 hnsB hsub' hb henvB hceB evB')
    | wildcard | literal _ | tuple _ | array _ | construct _ _ _ =>
      simp only [Peephole.fuseExpr] at ev
      rw [qualifyExprF_letValue] at ev ⊢
      cases ev with | letValue evV' hm evB' =>
        rename_i _ _ bs
        have evV := evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hnsV hsub hv henv hce evV'
        have hokV := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hv henv evV
        have hext := evV.heap_extends
        have hbs := patHasTy_matchPattern hp hokV hm
        have henvB := envOk_append hbs (henv.mono hext hext.length_le)
        have hdomB := matchPattern_names_of_simple hp.isSimple hm
        have hceB := constEnvOk_envRemove hdomB hp.dom_eq hce
        rw [patBoundVars_eq_patBoundNames hp.isSimple] at hceB
        exact .letValue evV hm
          (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs _ hlb.2 hnsB
            (fun k hk => List.mem_append_right _ (hsub k (envRemove_subset hk))) hb henvB hceB evB')
    | global _ _ | load _ | orElse _ _ _ | «repeat» _ _ | record _ _ | constructAs _ _ _ _ => cases hp
  | env, scope, Γ, locals, .matchValue s arms, _, h, h', r, hlb, hns, hsub,
      .matchValue hs harms, henv, hce, ev => by
    simp only [literalsBounded, Bool.and_eq_true] at hlb
    rcases hns with ⟨hnsS, hnsArms⟩
    simp only [Peephole.fuseExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | matchValue evS' hsel evB' =>
      have evS := evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hnsS hsub hs henv hce evS'
      have hokS := evalExpr_valOk_ext hnd hHas hProv hLib spec hWT hs henv evS
      have hext := evS.heap_extends
      rw [map_qualifyArmsF, fuseArms_eq_map, List.map_map] at hsel
      have hsel' : SourceSemantics.selectArm world [] _ _
          (arms.map fun arm => (qualifyPatF F arm.1,
            qualifyExprF F (Peephole.fuseExpr (Peephole.envRemove (Peephole.patBoundNames arm.1) env) arm.2))) =
          .ok (some (_, _)) := hsel
      obtain ⟨p, b, hmem, rfl, hm, hselOrig⟩ :=
        selectArm_mapBody (fun p b => Peephole.fuseExpr (Peephole.envRemove (Peephole.patBoundNames p) env) b) hsel'
      obtain ⟨Δ, hp, hb⟩ := harms.mem hmem
      have hlbB := literalsBounded_mem_arms hlb.2 hmem
      have ⟨_, hnsB⟩ := noLetShadowArms_mem hnsArms hmem
      have hbs := patHasTy_matchPattern hp hokS hm
      have henvB := envOk_append hbs (henv.mono hext hext.length_le)
      have hdomB := matchPattern_names_of_simple hp.isSimple hm
      have hceB := constEnvOk_envRemove hdomB hp.dom_eq hce
      rw [patBoundVars_eq_patBoundNames hp.isSimple] at hceB
      have hsub' : ∀ k ∈ (Peephole.envRemove (Peephole.patBoundNames p) env).map Prod.fst,
          k ∈ patBoundVars p ++ scope :=
        fun k hk => List.mem_append_right _ (hsub k (envRemove_subset hk))
      rw [← map_qualifyArmsF] at hselOrig
      exact .matchValue evS hselOrig
        (evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs _ hlbB hnsB hsub' hb henvB hceB evB')
termination_by _ _ _ _ e _ _ _ _ _ _ _ _ _ _ _ => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_fuseExpr_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ (env : Peephole.ConstEnv) {scope : List String} {Γ : TyEnv} {locals : Environment F Nat}
      {xs : List Expr} {ts : List Lower.Ty} {h h' : Heap F} {vs : List (SourceValue F)},
      literalsBoundedList xs = true →
      NoLetShadowList scope xs →
      (∀ k ∈ env.map Prod.fst, k ∈ scope) →
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      EnvOk enums h h.length Γ locals →
      ConstEnvOk env locals Γ →
      EvalArgs world [] locals ((Peephole.fuseList env xs).map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h'
  | _, _, _, _, _, _, _, _, _, _, _, _, .nil, _, _, ev => by cases ev; exact .nil
  | env, _, _, _, _, _, _, _, _, hlb, hns, hsub, .cons hd tl, henv, hce, ev => by
    simp only [literalsBoundedList, Bool.and_eq_true] at hlb
    rcases hns with ⟨_, hnsH, hnsT⟩
    cases ev with | cons evH evT =>
      have evH' := evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.1 hnsH hsub hd henv hce evH
      have hext := evH'.heap_extends
      exact .cons evH'
        (evalArgs_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs env hlb.2 hnsT hsub tl
          (henv.mono hext hext.length_le) hce evT)
termination_by _ _ _ _ xs _ _ _ _ _ _ _ _ _ _ _ => sizeOf xs

end

/-- **Stage 3 (`Peephole.rewriteExpr`) Full `UInt32` Backward Soundness:**
Composes Phase 2 (`lowerByteShifts`) and Phase 1 (`fuseExpr`) cleanly! -/
theorem evalExpr_peephole_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns)
    {scope : List String} {Γ : TyEnv} {locals : Environment F Nat}
    {e : Expr} {t : Lower.Ty} {h h' : Heap F} {r : SourceValue F}
    (hlb : literalsBounded e = true)
    (hns : NoLetShadow scope e)
    (hty : HasTy (fnSigsOf fns) enums Γ e t)
    (henv : EnvOk enums h h.length Γ locals)
    (ev : EvalExpr world [] locals (qualifyExprF F (Peephole.rewriteExpr e)) h r h') :
    EvalExpr world [] locals (qualifyExprF F e) h r h' := by
  have htyExt := hasTy_to_sigsWithU32OfField hSigs hty
  have htyFused := hasTy_fuseExpr hSigs [] htyExt
  have hlbFused := literalsBounded_fuseExpr [] hlb
  have evFused := evalExpr_lowerByteShifts_backward hnd hHas hProv hLib spec hWT hSigs []
    hlbFused htyFused henv (constEnvOk_nil locals Γ) ev
  exact evalExpr_fuseExpr_backward hnd hHas hProv hLib spec hWT hSigs []
    hlb hns (fun _ h => by cases h) htyExt henv (constEnvOk_nil locals Γ) evFused

end FuseExprEval

/-! #### Eliminating `sigsWithU32OfField` after `foldConstU32OfField` -/

mutual

/-- Every `u32_of_field` / `Prog::u32_of_field` call in `e` is a bounded constant
`u32_of_field (.literal n)` with `n < natLimit`. -/
def u32OfFieldIsConst : Expr → Bool
  | .call nm (some []) xs =>
    if nm == "u32_of_field" || nm == "Prog::u32_of_field" then
      match xs with
      | [.literal n] => nm == "u32_of_field" && decide (n < natLimit)
      | _ => false
    else u32OfFieldIsConstList xs
  | .call _ _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => u32OfFieldIsConstList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x => u32OfFieldIsConst x
  | .binary _ l r => u32OfFieldIsConst l && u32OfFieldIsConst r
  | .letValue _ v b => u32OfFieldIsConst v && u32OfFieldIsConst b
  | .matchValue s arms => u32OfFieldIsConst s && u32OfFieldIsConstArms arms
  | .literal _ | .var _ | .global _ _ => true

def u32OfFieldIsConstList : List Expr → Bool
  | [] => true
  | x :: xs => u32OfFieldIsConst x && u32OfFieldIsConstList xs

def u32OfFieldIsConstArms : List (Pat × Expr) → Bool
  | [] => true
  | (_, b) :: rest => u32OfFieldIsConst b && u32OfFieldIsConstArms rest

end

theorem u32OfFieldIsConst_call_args {nm : String} {targs : Option (List Lower.Ty)} {xs : List Expr}
    (h : u32OfFieldIsConst (.call nm targs xs) = true) :
    u32OfFieldIsConstList xs = true := by
  cases targs with
  | none => exact h
  | some ts =>
    cases ts with
    | cons _ _ => exact h
    | nil =>
      simp only [u32OfFieldIsConst] at h
      split at h
      · cases xs with
        | nil => cases h
        | cons x rest =>
          cases rest with
          | cons _ _ => simp at h
          | nil =>
            cases x <;> try cases h
            rfl
      · exact h

mutual

/-- If `u32_of_field` is not in `fnSigsOf fns`, any well-typed expression under `fnSigsOf fns`
contains no `u32_of_field` calls at all, hence satisfies `u32OfFieldIsConst = true`. -/
theorem u32OfFieldIsConst_of_hasTy_none {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hnone : fnSigsOf fns (qualified "u32_of_field") = none) :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy (fnSigsOf fns) enums Γ e t → u32OfFieldIsConst e = true
  | _, _, _, .literal | _, _, _, .var _ => rfl
  | _, _, _, .tuple items | _, _, _, .array _ items | _, _, _, .construct _ _ _ _ _ items
  | _, _, _, .builtin items => u32OfFieldIsConstList_of_hasTy_none hnone items
  | _, _, _, .repeat hx | _, _, _, .index hx | _, _, _, .project hx _ | _, _, _, .slice _ hx
  | _, _, _, .store hx | _, _, _, .load hx | _, _, _, .hint _ hx | _, _, _, .neg hx => by
    simpa [u32OfFieldIsConst] using u32OfFieldIsConst_of_hasTy_none hnone hx
  | _, _, _, .binary hl hr => by
    simp [u32OfFieldIsConst, u32OfFieldIsConst_of_hasTy_none hnone hl,
      u32OfFieldIsConst_of_hasTy_none hnone hr]
  | _, _, _, .letValue hx _ hb => by
    simp [u32OfFieldIsConst, u32OfFieldIsConst_of_hasTy_none hnone hx,
      u32OfFieldIsConst_of_hasTy_none hnone hb]
  | _, _, _, .matchValue hs harms => by
    simp [u32OfFieldIsConst, u32OfFieldIsConst_of_hasTy_none hnone hs,
      u32OfFieldIsConstArms_of_hasTy_none hnone harms]
  | _, _, _, .call (nm := nm) hsig items => by
    have hnot : (nm == "u32_of_field" || nm == "Prog::u32_of_field") = false := by
      cases hc : (nm == "u32_of_field" || nm == "Prog::u32_of_field")
      · rfl
      · simp only [Bool.or_eq_true, beq_iff_eq] at hc
        rcases hc with rfl | rfl <;>
          · rw [show qualifyName _ = qualified "u32_of_field" from rfl, hnone] at hsig; cases hsig
    simp [u32OfFieldIsConst, hnot, u32OfFieldIsConstList_of_hasTy_none hnone items]

theorem u32OfFieldIsConstList_of_hasTy_none {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hnone : fnSigsOf fns (qualified "u32_of_field") = none) :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList (fnSigsOf fns) enums Γ xs ts → u32OfFieldIsConstList xs = true
  | _, _, _, .nil => rfl
  | _, _, _, .cons hd tl => by
    simp [u32OfFieldIsConstList, u32OfFieldIsConst_of_hasTy_none hnone hd,
      u32OfFieldIsConstList_of_hasTy_none hnone tl]

theorem u32OfFieldIsConstArms_of_hasTy_none {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hnone : fnSigsOf fns (qualified "u32_of_field") = none) :
    ∀ {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms (fnSigsOf fns) enums Γ ts arms tb → u32OfFieldIsConstArms arms = true
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ hb tl => by
    simp [u32OfFieldIsConstArms, u32OfFieldIsConst_of_hasTy_none hnone hb,
      u32OfFieldIsConstArms_of_hasTy_none hnone tl]

end

theorem u32OfFieldIsConst_byteShuffleE {x : Expr} {slots : List (Option Nat)}
    (hx : u32OfFieldIsConst x = true) :
    u32OfFieldIsConst (Peephole.byteShuffleE x slots) = true := by
  have hslots : ∀ l : List (Option Nat),
      u32OfFieldIsConstList (l.map fun
        | some idx => .index (.var "__peep_b") idx
        | none => .var "__peep_z") = true := by
    intro l; induction l with
    | nil => rfl
    | cons o tl ih => cases o <;> simp [u32OfFieldIsConstList, u32OfFieldIsConst, ih]
  unfold Peephole.byteShuffleE Lower.letE Lower.callE Lower.litE Lower.vE
  simp [u32OfFieldIsConst, u32OfFieldIsConstList, hx]
  exact hslots slots

mutual

theorem u32OfFieldIsConst_lowerByteShifts :
    ∀ (env : Peephole.ConstEnv) {e : Expr},
      u32OfFieldIsConst e = true → u32OfFieldIsConst (Peephole.lowerByteShifts env e) = true
  | _, .literal _, _ | _, .var _, _ | _, .global _ _, _ => rfl
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h | env, .control _ x, h =>
    u32OfFieldIsConst_lowerByteShifts env (e := x) h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => u32OfFieldIsConst_lowerByteShiftsList env h
  | env, .binary _ l r, h => by
    simp only [Peephole.lowerByteShifts, u32OfFieldIsConst, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_lowerByteShifts env h.1, u32OfFieldIsConst_lowerByteShifts env h.2⟩
  | env, .letValue p v b, h => by
    simp only [u32OfFieldIsConst, Bool.and_eq_true] at h
    cases p <;> simp only [Peephole.lowerByteShifts, u32OfFieldIsConst, Bool.and_eq_true] <;>
      exact ⟨u32OfFieldIsConst_lowerByteShifts env h.1, u32OfFieldIsConst_lowerByteShifts _ h.2⟩
  | env, .matchValue s arms, h => by
    simp only [Peephole.lowerByteShifts, u32OfFieldIsConst, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_lowerByteShifts env h.1, u32OfFieldIsConst_lowerByteShiftsArms env h.2⟩
  | env, .call nm targs xs, h => by
    simp only [Peephole.lowerByteShifts]
    have hxs' := u32OfFieldIsConst_lowerByteShiftsList env (u32OfFieldIsConst_call_args h)
    cases htr : Peephole.tryLowerByteShift env nm targs (Peephole.lowerByteShiftsList env xs) with
    | some e' =>
      simp only [Option.getD_some]
      unfold Peephole.tryLowerByteShift at htr; split at htr
      · next x' c' heq =>
        rw [heq] at hxs'; simp only [u32OfFieldIsConstList, Bool.and_eq_true] at hxs'
        split at htr
        · cases hc : Peephole.extractU32Const? env c' with
          | none => simp [hc] at htr
          | some k =>
            rw [hc] at htr; simp only [Option.bind_some, Peephole.byteShrE] at htr
            split at htr
            · simp only [Option.some.injEq] at htr; subst htr; exact hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact u32OfFieldIsConst_byteShuffleE hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact u32OfFieldIsConst_byteShuffleE hxs'.1
            · simp only [Option.some.injEq] at htr; subst htr; exact u32OfFieldIsConst_byteShuffleE hxs'.1
            · cases htr
        · split at htr
          · cases hc : Peephole.extractU32Const? env c' with
            | none => simp [hc] at htr
            | some k =>
              rw [hc] at htr; simp only [Option.bind_some, Peephole.byteShlE] at htr
              split at htr
              · simp only [Option.some.injEq] at htr; subst htr; exact hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact u32OfFieldIsConst_byteShuffleE hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact u32OfFieldIsConst_byteShuffleE hxs'.1
              · simp only [Option.some.injEq] at htr; subst htr; exact u32OfFieldIsConst_byteShuffleE hxs'.1
              · cases htr
          · cases htr
      · cases htr
    | none =>
      simp only [Option.getD_none]
      cases targs with
      | none => exact hxs'
      | some ts =>
        cases ts with
        | cons _ _ => exact hxs'
        | nil =>
          simp only [u32OfFieldIsConst] at h ⊢
          cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hxs'
          | true =>
            simp only [h1, ↓reduceIte] at h ⊢
            cases xs with
            | nil => cases h
            | cons x rest =>
              cases rest with
              | cons _ _ => simp at h
              | nil =>
                cases x <;> try cases h
                simpa [Peephole.lowerByteShiftsList, Peephole.lowerByteShifts] using h
termination_by _ e _ => sizeOf e

theorem u32OfFieldIsConst_lowerByteShiftsList :
    ∀ (env : Peephole.ConstEnv) {xs : List Expr},
      u32OfFieldIsConstList xs = true → u32OfFieldIsConstList (Peephole.lowerByteShiftsList env xs) = true
  | _, [], _ => rfl
  | env, x :: xs, h => by
    simp only [Peephole.lowerByteShiftsList, u32OfFieldIsConstList, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_lowerByteShifts env h.1, u32OfFieldIsConst_lowerByteShiftsList env h.2⟩
termination_by _ xs _ => sizeOf xs

theorem u32OfFieldIsConst_lowerByteShiftsArms :
    ∀ (env : Peephole.ConstEnv) {arms : List (Pat × Expr)},
      u32OfFieldIsConstArms arms = true → u32OfFieldIsConstArms (Peephole.lowerByteShiftsArms env arms) = true
  | _, [], _ => rfl
  | env, (p, b) :: rest, h => by
    simp only [Peephole.lowerByteShiftsArms, u32OfFieldIsConstArms, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_lowerByteShifts _ h.1, u32OfFieldIsConst_lowerByteShiftsArms env h.2⟩
termination_by _ arms _ => sizeOf arms

end

theorem u32OfFieldIsConst_tryFuseCall {env : Peephole.ConstEnv}
    {nm : String} {targs : Option (List Lower.Ty)} {xs : List Expr} {e' : Expr}
    (htr : Peephole.tryFuseCall env nm targs xs = some e')
    (hxs : u32OfFieldIsConstList xs = true) :
    u32OfFieldIsConst e' = true := by
  unfold Peephole.tryFuseCall at htr; split at htr
  · next a b =>
    simp only [u32OfFieldIsConstList, Bool.and_eq_true] at hxs
    obtain ⟨ha, hb, _⟩ := hxs
    split at htr
    · cases hma : Peephole.matchAdd a with
      | some pab =>
        rcases pab with ⟨x, y⟩; rw [hma] at htr; simp only [Option.some.injEq] at htr; subst htr
        rw [matchAdd_eq hma] at ha; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at ha
        simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, ha.1, ha.2, hb]
      | none =>
        rw [hma] at htr; dsimp only at htr
        cases hmb : Peephole.matchAdd b with
        | none => simp [hmb] at htr
        | some pyz =>
          rcases pyz with ⟨y, z⟩; rw [hmb] at htr; simp only [Option.some.injEq] at htr; subst htr
          rw [matchAdd_eq hmb] at hb; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hb
          simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, ha, hb.1, hb.2]
    · split at htr
      · cases hr : Peephole.matchRotPair env a b with
        | none => simp [hr] at htr
        | some tr =>
          rcases tr with ⟨x, k1, k2⟩; rw [hr] at htr; dsimp only at htr
          have hxC : u32OfFieldIsConst x = true := by
            rcases (matchRotPair_inv hr).2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
              · obtain ⟨_, _, _, heq, _, _, _⟩ := matchShiftConst_inv h1
                rw [heq] at ha; have ha' := u32OfFieldIsConst_call_args ha
                simp only [u32OfFieldIsConstList, Bool.and_eq_true] at ha'; exact ha'.1
          cases hrot : Peephole.rotrFnOf? k1 k2 with
          | some rnm =>
            rw [hrot] at htr; simp only [Option.some.injEq] at htr; subst htr
            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
              simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hxC]
          | none =>
            rw [hrot] at htr; dsimp only at htr
            cases hxr : Peephole.xorRotrFnOf? k1 k2 with
            | none => simp [hxr] at htr
            | some xfn =>
              cases hxor : Peephole.matchXor x with
              | none => simp [hxr, hxor] at htr
              | some puv =>
                rcases puv with ⟨u, w⟩; rw [hxr, hxor] at htr
                simp only [Option.some.injEq] at htr; subst htr
                rw [matchXor_eq hxor] at hxC; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hxC
                rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                  simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hxC.1, hxC.2]
      · split at htr
        · next hsh =>
          cases b with
          | var vn =>
            dsimp only at htr
            cases hl : env.lookup vn with
            | none => simp [hl] at htr
            | some k =>
              rw [hl] at htr; simp only [Option.some.injEq] at htr; subst htr
              have hlt : k % 32 < natLimit := lt_trans (Nat.mod_lt k (by omega)) (by decide)
              simp only [Bool.or_eq_true, Peephole.isShrName, Peephole.isShlName, beq_iff_eq] at hsh
              rcases hsh with (rfl | rfl) | (rfl | rfl) <;>
                simp [Lower.callE, Lower.litE, u32OfFieldIsConst, u32OfFieldIsConstList, ha, hlt]
          | _ => cases htr
        · cases htr
  · cases htr

theorem u32OfFieldIsConst_tryFuseLet {env : Peephole.ConstEnv}
    {nm : String} {val body e' : Expr}
    (htr : Peephole.tryFuseLet env nm val body = some e')
    (hv : u32OfFieldIsConst val = true) (hb : u32OfFieldIsConst body = true) :
    u32OfFieldIsConst e' = true := by
  unfold Peephole.tryFuseLet at htr
  cases h1 : Peephole.tryDropDeadConst env nm val body with
  | some e =>
    rw [h1] at htr; simp only [Option.some.injEq] at htr; subst htr
    unfold Peephole.tryDropDeadConst at h1
    cases hc : Peephole.extractU32Const? env val with
    | none => simp [hc] at h1
    | some _ =>
      rw [hc] at h1; dsimp only at h1; split at h1
      · simp only [Option.some.injEq] at h1; subst h1; exact hb
      · cases h1
  | none =>
    rw [h1] at htr
    cases h2 : Peephole.tryFuseLetAdd3 nm val body with
    | some e =>
      rw [h2] at htr; simp only [Option.some.injEq] at htr; subst htr
      unfold Peephole.tryFuseLetAdd3 at h2
      cases ha : Peephole.matchAdd val with
      | none => simp [ha] at h2
      | some pab =>
        rcases pab with ⟨a, b⟩; rw [ha] at h2; dsimp only at h2
        rw [matchAdd_eq ha] at hv; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hv
        split at h2
        · next y rhs rest =>
          simp only [u32OfFieldIsConst, Bool.and_eq_true] at hb
          cases hr : Peephole.matchAdd rhs with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hb
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              simp [Lower.letE, Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2, hb.1.2, hb.2]
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                simp [Lower.letE, Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2, hb.1.1, hb.2]
              · cases h2
        · cases hr : Peephole.matchAdd body with
          | none => simp [hr] at h2
          | some pq =>
            rcases pq with ⟨p, q⟩; rw [hr] at h2; dsimp only at h2
            rw [matchAdd_eq hr] at hb; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hb
            split at h2
            · simp only [Option.some.injEq] at h2; subst h2
              simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2, hb.2]
            · split at h2
              · simp only [Option.some.injEq] at h2; subst h2
                simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2, hb.1]
              · cases h2
    | none =>
      rw [h2] at htr
      cases h3 : Peephole.tryFuseLetRotr env nm val body with
      | some e =>
        rw [h3] at htr; simp only [Option.some.injEq] at htr; subst htr
        unfold Peephole.tryFuseLetRotr at h3
        cases hs1 : Peephole.matchShiftConst env val with
        | none => simp [hs1] at h3
        | some t1 =>
          rcases t1 with ⟨d1, x1, k1⟩; rw [hs1] at h3; dsimp only at h3
          obtain ⟨_, _, _, hval, _, _, _⟩ := matchShiftConst_inv hs1
          rw [hval] at hv; have hv' := u32OfFieldIsConst_call_args hv
          simp only [u32OfFieldIsConstList, Bool.and_eq_true] at hv'
          split at h3
          · cases h3
          · split at h3
            · next s2 val2 body2 =>
              simp only [u32OfFieldIsConst, Bool.and_eq_true] at hb
              split at h3
              · cases h3
              · cases hs2 : Peephole.matchShiftConst env val2 with
                | none => simp [hs2] at h3
                | some t2 =>
                  rcases t2 with ⟨d2, x2, k2⟩; rw [hs2] at h3; dsimp only at h3
                  split at h3
                  · cases h3
                  · cases hrot : Peephole.rotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                    | none => simp [hrot] at h3
                    | some rnm =>
                      rw [hrot] at h3; dsimp only at h3
                      split at h3
                      · next y rhs rest =>
                        have hrest : u32OfFieldIsConst rest = true := by
                          have hb2 := hb.2; simp only [u32OfFieldIsConst, Bool.and_eq_true] at hb2; exact hb2.2
                        cases hor : Peephole.matchOr rhs with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                              simp [Lower.letE, Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv'.1, hrest]
                          · cases h3
                      · cases hor : Peephole.matchOr body2 with
                        | none => simp [hor] at h3
                        | some _ =>
                          rw [hor] at h3; dsimp only at h3; split at h3
                          · simp only [Option.some.injEq] at h3; subst h3
                            rcases rotrFnOf?_inv hrot with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                              simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv'.1]
                          · cases h3
            · cases h3
      | none =>
        rw [h3] at htr
        cases h4 : Peephole.tryFuseLetXorRotr4 env nm val body with
        | some e =>
          rw [h4] at htr; simp only [Option.some.injEq] at htr; subst htr
          unfold Peephole.tryFuseLetXorRotr4 at h4; split at h4
          · next a b s1 val1 s2 val2 body2 hx =>
            rw [matchXor_eq hx] at hv; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hv
            simp only [u32OfFieldIsConst, Bool.and_eq_true] at hb
            split at h4
            · cases h4
            · split at h4
              · next d1 _ k1 d2 _ k2 _ _ =>
                split at h4
                · cases h4
                · dsimp only at h4
                  cases hxr : Peephole.xorRotrFnOf? (if d1 = true then k1 else k2) (if d1 = true then k2 else k1) with
                  | none => simp [hxr] at h4
                  | some xfn =>
                    rw [hxr] at h4; dsimp only at h4
                    split at h4
                    · next y rhs rest =>
                      have hrest : u32OfFieldIsConst rest = true := by
                        have hb2 := hb.2.2; simp only [u32OfFieldIsConst, Bool.and_eq_true] at hb2; exact hb2.2
                      cases hor : Peephole.matchOr rhs with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                            simp [Lower.letE, Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2, hrest]
                        · cases h4
                    · cases hor : Peephole.matchOr body2 with
                      | none => simp [hor] at h4
                      | some _ =>
                        rw [hor] at h4; dsimp only at h4; split at h4
                        · simp only [Option.some.injEq] at h4; subst h4
                          rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                            simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2]
                        · cases h4
              · cases h4
          · cases h4
        | none =>
          rw [h4] at htr
          unfold Peephole.tryFuseLetXorRotrHalf at htr
          cases hx : Peephole.matchXor val with
          | none => simp [hx] at htr
          | some pab =>
            rcases pab with ⟨a, b⟩; rw [hx] at htr; dsimp only at htr
            rw [matchXor_eq hx] at hv; simp [u32OfFieldIsConst, u32OfFieldIsConstList] at hv
            split at htr
            · next y rhs rest =>
              simp only [u32OfFieldIsConst, Bool.and_eq_true] at hb
              cases hor : Peephole.matchOr rhs with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                        simp [Lower.letE, Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2, hb.2]
            · cases hor : Peephole.matchOr body with
              | none => simp [hor] at htr
              | some pe =>
                rcases pe with ⟨e1, e2⟩; rw [hor] at htr; dsimp only at htr
                cases hrp : Peephole.matchRotPair env e1 e2 with
                | none => simp [hrp] at htr
                | some tr =>
                  rcases tr with ⟨_, kShr, kShl⟩; rw [hrp] at htr; dsimp only at htr; split at htr
                  · cases htr
                  · cases hxr : Peephole.xorRotrFnOf? kShr kShl with
                    | none => simp [hxr] at htr
                    | some xfn =>
                      rw [hxr] at htr; simp only [Option.some.injEq] at htr; subst htr
                      rcases xorRotrFnOf?_inv hxr with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
                        simp [Lower.callE, u32OfFieldIsConst, u32OfFieldIsConstList, hv.1, hv.2]

mutual

theorem u32OfFieldIsConst_fuseExpr :
    ∀ (env : Peephole.ConstEnv) {e : Expr},
      u32OfFieldIsConst e = true → u32OfFieldIsConst (Peephole.fuseExpr env e) = true
  | _, .literal _, _ | _, .var _, _ | _, .global _ _, _ => rfl
  | env, .repeat x _, h | env, .index x _, h | env, .slice x _ _, h
  | env, .member x _, h | env, .project x _, h | env, .store x, h
  | env, .load x, h | env, .hint _ x _, h | env, .neg x, h | env, .control _ x, h =>
    u32OfFieldIsConst_fuseExpr env (e := x) h
  | env, .tuple xs, h | env, .array xs, h | env, .construct _ _ _ xs, h
  | env, .constructAs _ _ _ xs, h | env, .record _ xs, h | env, .update _ xs, h
  | env, .builtin _ xs, h => u32OfFieldIsConst_fuseList env h
  | env, .binary _ l r, h => by
    simp only [Peephole.fuseExpr, u32OfFieldIsConst, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_fuseExpr env h.1, u32OfFieldIsConst_fuseExpr env h.2⟩
  | env, .matchValue s arms, h => by
    simp only [Peephole.fuseExpr, u32OfFieldIsConst, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_fuseExpr env h.1, u32OfFieldIsConst_fuseArms env h.2⟩
  | env, .call nm targs xs, h => by
    simp only [Peephole.fuseExpr]
    have hxs' := u32OfFieldIsConst_fuseList env (u32OfFieldIsConst_call_args h)
    cases htr : Peephole.tryFuseCall env nm targs (Peephole.fuseList env xs) with
    | some e' =>
      simp only [Option.getD_some]; exact u32OfFieldIsConst_tryFuseCall htr hxs'
    | none =>
      simp only [Option.getD_none]
      cases targs with
      | none => exact hxs'
      | some ts =>
        cases ts with
        | cons _ _ => exact hxs'
        | nil =>
          simp only [u32OfFieldIsConst] at h ⊢
          cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hxs'
          | true =>
            simp only [h1, ↓reduceIte] at h ⊢
            cases xs with
            | nil => cases h
            | cons x rest =>
              cases rest with
              | cons _ _ => simp at h
              | nil =>
                cases x <;> try cases h
                simpa [Peephole.fuseList, Peephole.fuseExpr] using h
  | env, .letValue p v b, h => by
    simp only [u32OfFieldIsConst, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      simp only [Peephole.fuseExpr]
      let env' : Peephole.ConstEnv :=
        match Peephole.extractU32Const? env (Peephole.fuseExpr env v) with
        | some k => (nm, k) :: Peephole.envRemove [nm] env
        | none => Peephole.envRemove [nm] env
      have hv' := u32OfFieldIsConst_fuseExpr env h.1
      have hb' := u32OfFieldIsConst_fuseExpr env' h.2
      change u32OfFieldIsConst ((Peephole.tryFuseLet env nm (Peephole.fuseExpr env v)
          (Peephole.fuseExpr env' b)).getD _) = true
      cases htr : Peephole.tryFuseLet env nm (Peephole.fuseExpr env v) (Peephole.fuseExpr env' b) with
      | none => simp only [Option.getD_none, u32OfFieldIsConst, Bool.and_eq_true]; exact ⟨hv', hb'⟩
      | some e' => simp only [Option.getD_some]; exact u32OfFieldIsConst_tryFuseLet htr hv' hb'
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      simp only [Peephole.fuseExpr, u32OfFieldIsConst, Bool.and_eq_true]
      exact ⟨u32OfFieldIsConst_fuseExpr env h.1, u32OfFieldIsConst_fuseExpr _ h.2⟩
termination_by _ e _ => sizeOf e

theorem u32OfFieldIsConst_fuseList :
    ∀ (env : Peephole.ConstEnv) {xs : List Expr},
      u32OfFieldIsConstList xs = true → u32OfFieldIsConstList (Peephole.fuseList env xs) = true
  | _, [], _ => rfl
  | env, x :: xs, h => by
    simp only [Peephole.fuseList, u32OfFieldIsConstList, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_fuseExpr env h.1, u32OfFieldIsConst_fuseList env h.2⟩
termination_by _ xs _ => sizeOf xs

theorem u32OfFieldIsConst_fuseArms :
    ∀ (env : Peephole.ConstEnv) {arms : List (Pat × Expr)},
      u32OfFieldIsConstArms arms = true → u32OfFieldIsConstArms (Peephole.fuseArms env arms) = true
  | _, [], _ => rfl
  | env, (p, b) :: rest, h => by
    simp only [Peephole.fuseArms, u32OfFieldIsConstArms, Bool.and_eq_true] at h ⊢
    exact ⟨u32OfFieldIsConst_fuseExpr _ h.1, u32OfFieldIsConst_fuseArms env h.2⟩
termination_by _ arms _ => sizeOf arms

end

mutual

/-- After `foldConstU32OfField`, any expression typed under `sigsWithU32OfField (fnSigsOf fns)`
with `u32OfFieldIsConst e = true` is well-typed directly under `fnSigsOf fns`! -/
theorem hasTy_foldConstU32OfField_of_const {fns : List Fn} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      u32OfFieldIsConst e = true →
      HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ e t →
      HasTy (fnSigsOf fns) enums Γ (foldConstU32OfField e) t
  | _, _, _, _, .literal => .literal
  | _, _, _, _, .var hl => .var hl
  | _, _, _, hc, .tuple items => .tuple (hasTy_foldConstU32OfFieldList_of_const hc items)
  | _, _, _, hc, .array hlen items =>
    .array (by rw [foldConstU32OfFieldList_length]; exact hlen)
      (hasTy_foldConstU32OfFieldList_of_const hc items)
  | _, _, _, hc, .repeat hx => .repeat (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .index hx => .index (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .project hx hget => .project (hasTy_foldConstU32OfField_of_const hc hx) hget
  | _, _, _, hc, .slice hnot hx => .slice hnot (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .construct h1 h2 h3 h4 hctor items =>
    .construct h1 h2 h3 h4 hctor (hasTy_foldConstU32OfFieldList_of_const hc items)
  | _, _, _, hc, .builtin items => .builtin (hasTy_foldConstU32OfFieldList_of_const hc items)
  | _, _, _, hc, .store hx => .store (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .load hx => .load (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .hint hfo hx => .hint hfo (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .neg hx => .neg (hasTy_foldConstU32OfField_of_const hc hx)
  | _, _, _, hc, .binary hl hr => by
    simp only [u32OfFieldIsConst, Bool.and_eq_true] at hc
    exact .binary (hasTy_foldConstU32OfField_of_const hc.1 hl)
      (hasTy_foldConstU32OfField_of_const hc.2 hr)
  | _, _, _, hc, .letValue hx hp hb => by
    simp only [u32OfFieldIsConst, Bool.and_eq_true] at hc
    exact .letValue (hasTy_foldConstU32OfField_of_const hc.1 hx) hp
      (hasTy_foldConstU32OfField_of_const hc.2 hb)
  | _, _, _, hc, .matchValue hs harms => by
    simp only [u32OfFieldIsConst, Bool.and_eq_true] at hc
    exact .matchValue (hasTy_foldConstU32OfField_of_const hc.1 hs)
      (hasTy_foldConstU32OfFieldArms_of_const hc.2 harms)
  | _, .call nm (some []) xs, _, hc, .call hsig items => by
    by_cases hq : qualifyName nm = qualified "u32_of_field"
    · rw [hq, sigsWithU32OfField_u32_of_field] at hsig
      simp only [Option.some.injEq, Prod.mk.injEq] at hsig
      obtain ⟨_, rfl⟩ := hsig
      have hnm : (nm == "u32_of_field" || nm == "Prog::u32_of_field") = true := by
        unfold qualifyName qualified moduleName at hq
        split at hq
        · simp [hq]
        · have heq : nm = "u32_of_field" := qualified_inj hq
          simp [heq]
      simp only [u32OfFieldIsConst, hnm, ↓reduceIte] at hc
      cases xs with
      | nil => cases hc
      | cons x rest =>
        cases rest with
        | cons _ _ => simp at hc
        | nil =>
          cases x <;> try cases hc
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          obtain ⟨rfl, hlt⟩ := hc
          simp only [foldConstU32OfField, hlt, ↓reduceIte]
          refine .call (ptys := [.array .field 4]) ?_ ?_
          · rw [TypedGadgets.qualifyName_u32_from_fields, fnSigsOf_nonProg fns rfl]; rfl
          · exact .cons (.array rfl (.cons .literal (.cons .literal (.cons .literal (.cons .literal .nil))))) .nil
    · rw [sigsWithU32OfField_of_ne _ hq] at hsig
      have hxs := u32OfFieldIsConst_call_args hc
      unfold foldConstU32OfField
      split
      · next n =>
        exfalso; exact hq rfl
      · exact .call hsig (hasTy_foldConstU32OfFieldList_of_const hxs items)
termination_by _ e _ _ _ => sizeOf e

theorem hasTy_foldConstU32OfFieldList_of_const {fns : List Fn} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      u32OfFieldIsConstList xs = true →
      HasTyList (sigsWithU32OfField (fnSigsOf fns)) enums Γ xs ts →
      HasTyList (fnSigsOf fns) enums Γ (foldConstU32OfFieldList xs) ts
  | _, _, _, _, .nil => .nil
  | _, _, _, hc, .cons hd tl => by
    simp only [u32OfFieldIsConstList, Bool.and_eq_true] at hc
    exact .cons (hasTy_foldConstU32OfField_of_const hc.1 hd)
      (hasTy_foldConstU32OfFieldList_of_const hc.2 tl)
termination_by _ xs _ _ _ => sizeOf xs

theorem hasTy_foldConstU32OfFieldArms_of_const {fns : List Fn} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      u32OfFieldIsConstArms arms = true →
      HasTyArms (sigsWithU32OfField (fnSigsOf fns)) enums Γ ts arms tb →
      HasTyArms (fnSigsOf fns) enums Γ ts (foldConstU32OfFieldArms arms) tb
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, hc, .cons hp hb tl => by
    simp only [u32OfFieldIsConstArms, Bool.and_eq_true] at hc
    exact .cons hp (hasTy_foldConstU32OfField_of_const hc.1 hb)
      (hasTy_foldConstU32OfFieldArms_of_const hc.2 tl)
termination_by _ _ _ arms _ _ => sizeOf arms

end

/-- **Unified `HasTy` Preservation for `foldConstU32OfField ∘ Peephole.rewriteExpr`:**
Works uniformly whether or not `u32_of_field` is present in `fns`! -/
theorem hasTy_foldConst_rewriteExpr {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) {Γ : TyEnv} {e : Expr} {t : Lower.Ty}
    (hty : HasTy (fnSigsOf fns) enums Γ e t) :
    HasTy (fnSigsOf fns) enums Γ (foldConstU32OfField (Peephole.rewriteExpr e)) t := by
  have htyRw : HasTy (sigsWithU32OfField (fnSigsOf fns)) enums Γ (Peephole.rewriteExpr e) t :=
    hasTy_lowerByteShifts hSigs [] (hasTy_fuseExpr hSigs [] (hasTy_to_sigsWithU32OfField hSigs hty))
  cases huf : fnSigsOf fns (qualified "u32_of_field") with
  | some p =>
    rcases p with ⟨pts, rt⟩
    obtain ⟨rfl, rfl⟩ := hSigs.1 pts rt huf
    have hback : HasTy (fnSigsOf fns) enums Γ (Peephole.rewriteExpr e) t := by
      refine hasTy_mono_sigs ?_ htyRw
      intro qnm v hv
      by_cases hq : qnm = qualified "u32_of_field"
      · subst hq; rw [sigsWithU32OfField_u32_of_field] at hv; rw [huf]; exact hv
      · rwa [sigsWithU32OfField_of_ne _ hq] at hv
    exact hasTy_foldConstU32OfField hSigs hback
  | none =>
    have hc0 := u32OfFieldIsConst_of_hasTy_none huf hty
    have hc1 := u32OfFieldIsConst_fuseExpr [] hc0
    have hc2 := u32OfFieldIsConst_lowerByteShifts [] hc1
    exact hasTy_foldConstU32OfField_of_const hc2 htyRw

end PeepholeProof

/-! ## Section 7: Stage 5 (`inlineCallsM` & `prefixExpr` Alpha-Renaming) Backward Soundness -/

section InlineCallsProof

/-! ### Part 7A: Prefix Algebra (`inlinePfx`, `inlinePfx_inj`, `NoPrefixGe`) -/

/-- Exact alpha-renaming prefix emitted by `inlineCallsM` at counter value `k`. -/
def inlinePfx (k : Nat) : String := s!"_i{k}_"

private theorem inlinePfx_eq (k : Nat) : inlinePfx k = "_i" ++ Nat.repr k ++ "_" := rfl

theorem string_append_left_inj {pfx a b : String} (h : pfx ++ a = pfx ++ b) : a = b := by
  have h1 := congrArg String.toList h
  simp only [String.toList_append] at h1
  exact String.ext (List.append_cancel_left h1)

private def parseDecDigits (acc : Nat) : List Char → Nat :=
  List.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) acc

private theorem digitChar_parse {d : Nat} (hd : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d ∧ Nat.digitChar d ≠ '_' := by
  match d, hd with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide
  | _ + 10, h => omega

private theorem toDigitsCore_spec :
    ∀ (fuel n : Nat) (ds : List Char), n < fuel → (∀ c ∈ ds, c ≠ '_') →
      (∀ c ∈ Nat.toDigitsCore 10 fuel n ds, c ≠ '_') ∧
      parseDecDigits 0 (Nat.toDigitsCore 10 fuel n ds) = parseDecDigits n ds
  | 0, _, _, hlt, _ => by omega
  | fuel + 1, n, ds, hlt, hds => by
    simp only [Nat.toDigitsCore]
    have hdLt : n % 10 < 10 := Nat.mod_lt n (by omega)
    obtain ⟨hdParse, hdNe⟩ := digitChar_parse hdLt
    by_cases hz : n / 10 = 0
    · simp only [hz, ↓reduceIte]
      have hnEq : n = n % 10 := by omega
      refine ⟨fun c hc => ?_, ?_⟩
      · rcases List.mem_cons.mp hc with rfl | htl
        · exact hdNe
        · exact hds c htl
      · simp only [parseDecDigits, List.foldl_cons, Nat.zero_mul, Nat.zero_add, hdParse]
        rw [← hnEq]
    · simp only [hz, ↓reduceIte]
      have hdivLt : n / 10 < fuel := by omega
      have hds' : ∀ c ∈ Nat.digitChar (n % 10) :: ds, c ≠ '_' := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | htl
        · exact hdNe
        · exact hds c htl
      obtain ⟨hchars, hparse⟩ := toDigitsCore_spec fuel (n / 10) (Nat.digitChar (n % 10) :: ds) hdivLt hds'
      refine ⟨hchars, ?_⟩
      rw [hparse]
      simp only [parseDecDigits, List.foldl_cons, hdParse]
      have hrecomp : n / 10 * 10 + n % 10 = n := by omega
      rw [hrecomp]

private theorem nat_repr_spec (k : Nat) :
    (∀ c ∈ (Nat.repr k).toList, c ≠ '_') ∧ parseDecDigits 0 (Nat.repr k).toList = k := by
  have h := toDigitsCore_spec (k + 1) k [] (Nat.lt_succ_self k) (fun _ hc => by cases hc)
  simpa [Nat.repr, Nat.toDigits, parseDecDigits] using h

private theorem list_append_sep_inj {α : Type} {sep : α} :
    ∀ {l1 l2 r1 r2 : List α},
      (∀ x ∈ l1, x ≠ sep) → (∀ x ∈ l2, x ≠ sep) →
      l1 ++ sep :: r1 = l2 ++ sep :: r2 → l1 = l2 ∧ r1 = r2
  | [], [], _, _, _, _, heq => by
    simp only [List.nil_append, List.cons.injEq] at heq; exact ⟨rfl, heq.2⟩
  | [], h :: _, _, _, _, h2, heq => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1.symm (h2 h List.mem_cons_self)
  | h :: _, [], _, _, h1, _, heq => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 (h1 h List.mem_cons_self)
  | a :: t1, b :: t2, r1, r2, h1, h2, heq => by
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, htl⟩ := heq
    obtain ⟨hl, hr⟩ := list_append_sep_inj
      (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) htl
    exact ⟨congrArg (a :: ·) hl, hr⟩

/-- `inlinePfx` is jointly injective on both the counter id and the suffix! -/
theorem inlinePfx_inj {k1 k2 : Nat} {r1 r2 : String}
    (h : inlinePfx k1 ++ r1 = inlinePfx k2 ++ r2) : k1 = k2 ∧ r1 = r2 := by
  rw [inlinePfx_eq, inlinePfx_eq] at h
  have h1 := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at h1
  have h2 : (Nat.repr k1).toList ++ ('_' :: r1.toList) = (Nat.repr k2).toList ++ ('_' :: r2.toList) := by
    have hdrop := List.append_cancel_left (as := ['_', 'i']) (by simpa [List.append_assoc] using h1)
    simpa [List.append_assoc] using hdrop
  obtain ⟨hchars1, hparse1⟩ := nat_repr_spec k1
  obtain ⟨hchars2, hparse2⟩ := nat_repr_spec k2
  obtain ⟨hrepr, hr⟩ := list_append_sep_inj hchars1 hchars2 h2
  refine ⟨?_, String.ext hr⟩
  rw [← hparse1, ← hparse2, hrepr]

/-- String `s` does not carry any inline-prefix `_i{k}_` with `k ≥ c`. -/
def NoPrefixGe (c : Nat) (s : String) : Prop :=
  ∀ k, c ≤ k → ∀ rest, s ≠ inlinePfx k ++ rest

theorem NoPrefixGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) {s : String} (h : NoPrefixGe c1 s) :
    NoPrefixGe c2 s :=
  fun k hk => h k (Nat.le_trans hle hk)

theorem noPrefixGe_inlinePfx_lt {k c : Nat} (hlt : k < c) (u : String) :
    NoPrefixGe c (inlinePfx k ++ u) := by
  intro k' hk' rest heq
  obtain ⟨rfl, _⟩ := inlinePfx_inj heq
  omega

theorem ne_inlinePfx_of_noPrefixGe {c k : Nat} {s : String}
    (h : NoPrefixGe c s) (hle : c ≤ k) (u : String) : s ≠ inlinePfx k ++ u :=
  h k hle u

/-- All free and bound variables in `e` satisfy `NoPrefixGe c`. -/
def ExprNoPrefixGe (c : Nat) (e : Expr) : Prop :=
  (∀ v, hasFreeVar v e = true → NoPrefixGe c v) ∧
  (∀ v, hasBoundVar v e = true → NoPrefixGe c v)

def ListNoPrefixGe (c : Nat) (xs : List Expr) : Prop :=
  (∀ v, hasFreeVarList v xs = true → NoPrefixGe c v) ∧
  (∀ v, hasBoundVarList v xs = true → NoPrefixGe c v)

def ArmsNoPrefixGe (c : Nat) (arms : List (Pat × Expr)) : Prop :=
  (∀ v, hasFreeVarArms v arms = true → NoPrefixGe c v) ∧
  (∀ v, hasBoundVarArms v arms = true → NoPrefixGe c v)

theorem ExprNoPrefixGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) {e : Expr} (h : ExprNoPrefixGe c1 e) :
    ExprNoPrefixGe c2 e :=
  ⟨fun v hv => (h.1 v hv).mono hle, fun v hv => (h.2 v hv).mono hle⟩

theorem ListNoPrefixGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) {xs : List Expr} (h : ListNoPrefixGe c1 xs) :
    ListNoPrefixGe c2 xs :=
  ⟨fun v hv => (h.1 v hv).mono hle, fun v hv => (h.2 v hv).mono hle⟩

theorem ArmsNoPrefixGe.mono {c1 c2 : Nat} (hle : c1 ≤ c2) {arms : List (Pat × Expr)}
    (h : ArmsNoPrefixGe c1 arms) : ArmsNoPrefixGe c2 arms :=
  ⟨fun v hv => (h.1 v hv).mono hle, fun v hv => (h.2 v hv).mono hle⟩

theorem exprNoPrefixGe_letValue_rhs {c : Nat} {p : Pat} {x b : Expr}
    (h : ExprNoPrefixGe c (.letValue p x b)) : ExprNoPrefixGe c x :=
  ⟨fun v hv => h.1 v (by simp [hasFreeVar, hv]),
   fun v hv => h.2 v (by simp [hasBoundVar, hv])⟩

theorem exprNoPrefixGe_letValue_body {c : Nat} {p : Pat} {x b : Expr}
    (h : ExprNoPrefixGe c (.letValue p x b)) : ExprNoPrefixGe c b := by
  refine ⟨fun v hv => ?_, fun v hv => h.2 v (by simp [hasBoundVar, hv])⟩
  by_cases hp : v ∈ patBoundVars p
  · exact h.2 v (by simp [hasBoundVar, hp])
  · exact h.1 v (by simp [hasFreeVar, hp, hv])

theorem exprNoPrefixGe_matchValue_scrut {c : Nat} {s : Expr} {arms : List (Pat × Expr)}
    (h : ExprNoPrefixGe c (.matchValue s arms)) : ExprNoPrefixGe c s :=
  ⟨fun v hv => h.1 v (by simp [hasFreeVar, hv]),
   fun v hv => h.2 v (by simp [hasBoundVar, hv])⟩

theorem armsNoPrefixGe_matchValue {c : Nat} {s : Expr} {arms : List (Pat × Expr)}
    (h : ExprNoPrefixGe c (.matchValue s arms)) : ArmsNoPrefixGe c arms :=
  ⟨fun v hv => h.1 v (by simp [hasFreeVar, hv]),
   fun v hv => h.2 v (by simp [hasBoundVar, hv])⟩

theorem exprNoPrefixGe_arm_body {c : Nat} {p : Pat} {b : Expr} {rest : List (Pat × Expr)}
    (h : ArmsNoPrefixGe c ((p, b) :: rest)) : ExprNoPrefixGe c b := by
  refine ⟨fun v hv => ?_, fun v hv => h.2 v (by simp [hasBoundVarArms, hv])⟩
  by_cases hp : v ∈ patBoundVars p
  · exact h.2 v (by simp [hasBoundVarArms, hp])
  · exact h.1 v (by simp [hasFreeVarArms, hp, hv])

theorem armsNoPrefixGe_tail {c : Nat} {p : Pat} {b : Expr} {rest : List (Pat × Expr)}
    (h : ArmsNoPrefixGe c ((p, b) :: rest)) : ArmsNoPrefixGe c rest :=
  ⟨fun v hv => h.1 v (by simp [hasFreeVarArms, hv]),
   fun v hv => h.2 v (by simp [hasBoundVarArms, hv])⟩

/-! ### Part 7B: `noInlinableInBoundedCalls`, `allDistinct → Nodup`, & `hasFreeVar_of_hasTy` -/

mutual

/-- Syntactic predicate: every `u32_of_field`, `Prog::u32_of_field`, and `UInt32::from_field`
argument contains no calls to inlinable `f*`/`jp*` functions (so `inlineCallsM` is the identity
on bounded-literal call arguments, preserving `literalsBounded` unconditionally). -/
def noInlinableInBoundedCalls : Expr → Bool
  | .call nm (some []) [arg] =>
    if nm == "u32_of_field" || nm == "Prog::u32_of_field" || nm == "UInt32::from_field" then
      noInlinableCalls arg
    else
      noInlinableInBoundedCalls arg
  | .call _ _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs
  | .record _ xs | .update _ xs | .builtin _ xs => noInlinableInBoundedCallsList xs
  | .repeat x _ | .index x _ | .slice x _ _ | .member x _ | .project x _
  | .store x | .load x | .hint _ x _ | .neg x | .control _ x => noInlinableInBoundedCalls x
  | .binary _ l r => noInlinableInBoundedCalls l && noInlinableInBoundedCalls r
  | .letValue _ v b => noInlinableInBoundedCalls v && noInlinableInBoundedCalls b
  | .matchValue s arms => noInlinableInBoundedCalls s && noInlinableInBoundedCallsArms arms
  | .literal _ | .var _ | .global _ _ => true

def noInlinableInBoundedCallsList : List Expr → Bool
  | [] => true
  | x :: xs => noInlinableInBoundedCalls x && noInlinableInBoundedCallsList xs

def noInlinableInBoundedCallsArms : List (Pat × Expr) → Bool
  | [] => true
  | (_, b) :: rest => noInlinableInBoundedCalls b && noInlinableInBoundedCallsArms rest

end

mutual

theorem noInlinableInBoundedCalls_of_noInlinableCalls :
    ∀ {e : Expr}, noInlinableCalls e = true → noInlinableInBoundedCalls e = true
  | .literal _, _ | .var _, _ | .global _ _, _ => rfl
  | .repeat x _, h | .index x _, h | .slice x _ _, h | .member x _, h | .project x _, h
  | .store x, h | .load x, h | .hint _ x _, h | .neg x, h | .control _ x, h =>
    noInlinableInBoundedCalls_of_noInlinableCalls (e := x) h
  | .tuple xs, h | .array xs, h | .construct _ _ _ xs, h | .constructAs _ _ _ xs, h
  | .record _ xs, h | .update _ xs, h | .builtin _ xs, h =>
    noInlinableInBoundedCallsList_of_noInlinableCalls h
  | .binary _ l r, h => by
    simp only [noInlinableCalls, noInlinableInBoundedCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_of_noInlinableCalls h.1,
           noInlinableInBoundedCalls_of_noInlinableCalls h.2⟩
  | .letValue _ v b, h => by
    simp only [noInlinableCalls, noInlinableInBoundedCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_of_noInlinableCalls h.1,
           noInlinableInBoundedCalls_of_noInlinableCalls h.2⟩
  | .matchValue s arms, h => by
    simp only [noInlinableCalls, noInlinableInBoundedCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_of_noInlinableCalls h.1,
           noInlinableInBoundedCallsArms_of_noInlinableCalls h.2⟩
  | .call nm targs xs, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    cases targs with
    | none => exact noInlinableInBoundedCallsList_of_noInlinableCalls h.2
    | some ts =>
      cases ts with
      | cons _ _ => exact noInlinableInBoundedCallsList_of_noInlinableCalls h.2
      | nil =>
        cases xs with
        | nil => rfl
        | cons x rest =>
          cases rest with
          | cons _ _ => exact noInlinableInBoundedCallsList_of_noInlinableCalls h.2
          | nil =>
            simp only [noInlinableCallsList, Bool.and_true] at h
            simp only [noInlinableInBoundedCalls]
            split
            · exact h.2
            · exact noInlinableInBoundedCalls_of_noInlinableCalls h.2
termination_by e _ => sizeOf e

theorem noInlinableInBoundedCallsList_of_noInlinableCalls :
    ∀ {xs : List Expr}, noInlinableCallsList xs = true → noInlinableInBoundedCallsList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [noInlinableCallsList, noInlinableInBoundedCallsList, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_of_noInlinableCalls h.1,
           noInlinableInBoundedCallsList_of_noInlinableCalls h.2⟩
termination_by xs _ => sizeOf xs

theorem noInlinableInBoundedCallsArms_of_noInlinableCalls :
    ∀ {arms : List (Pat × Expr)}, noInlinableCallsArms arms = true → noInlinableInBoundedCallsArms arms = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [noInlinableCallsArms, noInlinableInBoundedCallsArms, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_of_noInlinableCalls h.1,
           noInlinableInBoundedCallsArms_of_noInlinableCalls h.2⟩
termination_by arms _ => sizeOf arms

end

theorem noInlinableInBoundedCalls_call_args {nm : String} {targs : Option (List Lower.Ty)} {xs : List Expr}
    (h : noInlinableInBoundedCalls (.call nm targs xs) = true) :
    noInlinableInBoundedCallsList xs = true := by
  cases targs with
  | none => exact h
  | some ts =>
    cases ts with
    | cons _ _ => exact h
    | nil =>
      cases xs with
      | nil => rfl
      | cons x rest =>
        cases rest with
        | cons _ _ => exact h
        | nil =>
          simp only [noInlinableInBoundedCalls] at h
          simp only [noInlinableInBoundedCallsList, Bool.and_true]
          split at h
          · exact noInlinableInBoundedCalls_of_noInlinableCalls h
          · exact h

theorem nodup_of_allDistinct : ∀ {l : List String}, Lower.allDistinct l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [Lower.allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, nodup_of_allDistinct h.2⟩
    have := List.contains_iff_mem.mpr hmem
    rw [this] at h; cases h.1

private theorem lookup_append_of_not_mem_poly {α : Type} :
    ∀ {l1 l2 : List (String × α)} {x : String},
      x ∉ l1.map Prod.fst → (l1 ++ l2).lookup x = l2.lookup x
  | [], _, _, _ => rfl
  | (k, _) :: tl, l2, x, hnot => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.cons_append, List.lookup, beq_false_of_ne hnot.1]
    exact lookup_append_of_not_mem_poly hnot.2

private theorem lookup_append_of_mem_poly {α : Type} :
    ∀ {l1 l2 : List (String × α)} {x : String},
      x ∈ l1.map Prod.fst → (l1 ++ l2).lookup x = l1.lookup x
  | [], _, _, hmem => by cases hmem
  | (k, _) :: tl, l2, x, hmem => by
    simp only [List.cons_append, List.lookup]
    by_cases hx : x = k
    · subst hx; simp
    · simp only [beq_false_of_ne hx]
      simp only [List.map_cons, List.mem_cons] at hmem
      exact lookup_append_of_mem_poly (hmem.resolve_left hx)

private theorem find?_append_of_not_mem_poly {α : Type} :
    ∀ {l1 l2 : List (String × α)} {x : String},
      x ∉ l1.map Prod.fst → (l1 ++ l2).find? (·.1 == x) = l2.find? (·.1 == x)
  | [], _, _, _ => rfl
  | (k, _) :: tl, l2, x, hnot => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.cons_append, List.find?_cons, beq_false_of_ne (Ne.symm hnot.1)]
    exact find?_append_of_not_mem_poly hnot.2

private theorem find?_append_of_mem_poly {α : Type} :
    ∀ {l1 l2 : List (String × α)} {x : String},
      x ∈ l1.map Prod.fst → (l1 ++ l2).find? (·.1 == x) = l1.find? (·.1 == x)
  | [], _, _, hmem => by cases hmem
  | (k, _) :: tl, l2, x, hmem => by
    simp only [List.cons_append, List.find?_cons]
    by_cases hx : k = x
    · subst hx; simp
    · simp only [beq_false_of_ne hx]
      simp only [List.map_cons, List.mem_cons] at hmem
      exact find?_append_of_mem_poly (hmem.resolve_left (Ne.symm hx))

theorem lookup_reverse_of_nodup {α : Type} :
    ∀ {l : List (String × α)}, (l.map Prod.fst).Nodup →
      ∀ x, l.reverse.lookup x = l.lookup x
  | [], _, _ => rfl
  | (k, v) :: tl, hnd, x => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.reverse_cons, List.lookup]
    by_cases hx : x = k
    · subst hx
      rw [lookup_append_of_not_mem_poly (by rw [List.map_reverse]; exact fun hm => hnd.1 (List.mem_reverse.mp hm))]
      simp
    · rw [beq_false_of_ne hx]
      by_cases hmem : x ∈ tl.map Prod.fst
      · have hmemRev : x ∈ tl.reverse.map Prod.fst := by rw [List.map_reverse]; exact List.mem_reverse.mpr hmem
        rw [lookup_append_of_mem_poly hmemRev, lookup_reverse_of_nodup hnd.2]
      · have hnotRev : x ∉ tl.reverse.map Prod.fst := by
          rw [List.map_reverse]; exact fun hm => hmem (List.mem_reverse.mp hm)
        rw [lookup_append_of_not_mem_poly hnotRev, lookup_none_of_not_mem hmem]
        simp only [List.lookup, beq_false_of_ne hx]
where
  lookup_none_of_not_mem {α : Type} :
      ∀ {l : List (String × α)} {x : String}, x ∉ l.map Prod.fst → l.lookup x = none
    | [], _, _ => rfl
    | (k, _) :: tl, x, hnot => by
      simp only [List.map_cons, List.mem_cons, not_or] at hnot
      simp only [List.lookup, beq_false_of_ne hnot.1]
      exact lookup_none_of_not_mem hnot.2

theorem find?_reverse_of_nodup {α : Type} :
    ∀ {l : List (String × α)}, (l.map Prod.fst).Nodup →
      ∀ x, l.reverse.find? (·.1 == x) = l.find? (·.1 == x)
  | [], _, _ => rfl
  | (k, v) :: tl, hnd, x => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.reverse_cons, List.find?_cons]
    by_cases hx : k = x
    · subst hx
      rw [find?_append_of_not_mem_poly (by rw [List.map_reverse]; exact fun hm => hnd.1 (List.mem_reverse.mp hm))]
      simp
    · rw [beq_false_of_ne hx]
      by_cases hmem : x ∈ tl.map Prod.fst
      · have hmemRev : x ∈ tl.reverse.map Prod.fst := by rw [List.map_reverse]; exact List.mem_reverse.mpr hmem
        rw [find?_append_of_mem_poly hmemRev, find?_reverse_of_nodup hnd.2]
      · have hnotRev : x ∉ tl.reverse.map Prod.fst := by
          rw [List.map_reverse]; exact fun hm => hmem (List.mem_reverse.mp hm)
        rw [find?_append_of_not_mem_poly hnotRev]
        have hnone : tl.find? (·.1 == x) = none := by
          rw [List.find?_eq_none]
          intro p hp
          cases hpx : (p.1 == x)
          · exact Bool.false_ne_true
          · simp only [beq_iff_eq] at hpx
            exact absurd (hpx ▸ List.mem_map.mpr ⟨p, hp, rfl⟩) hmem
        simp only [List.find?_cons, beq_false_of_ne hx, List.find?_nil, hnone]

mutual

/-- Every free variable of a well-typed expression is bound in `Γ`. -/
theorem hasFreeVar_of_hasTy {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy sigs enums Γ e t → ∀ x, hasFreeVar x e = true → x ∈ Γ.map Prod.fst
  | _, _, _, .literal, _, hx => by simp [hasFreeVar] at hx
  | Γ, .var y, _, .var hl, x, hx => by
    simp only [hasFreeVar, beq_iff_eq] at hx; subst hx
    induction Γ with
    | nil => cases hl
    | cons hd tl ih =>
      rcases hd with ⟨k, _⟩
      simp only [List.lookup] at hl
      simp only [List.map_cons, List.mem_cons]
      by_cases hxk : y = k
      · exact Or.inl hxk
      · simp only [beq_false_of_ne hxk] at hl
        exact Or.inr (ih hl)
  | _, _, _, .tuple items, x, hx | _, _, _, .array _ items, x, hx
  | _, _, _, .construct _ _ _ _ _ items, x, hx | _, _, _, .builtin items, x, hx
  | _, _, _, .call _ items, x, hx => hasFreeVar_of_hasTyList items x hx
  | _, _, _, .repeat h, x, hx | _, _, _, .index h, x, hx | _, _, _, .project h _, x, hx
  | _, _, _, .slice _ h, x, hx | _, _, _, .store h, x, hx | _, _, _, .load h, x, hx
  | _, _, _, .hint _ h, x, hx | _, _, _, .neg h, x, hx => hasFreeVar_of_hasTy h x hx
  | _, _, _, .binary hl hr, x, hx => by
    simp only [hasFreeVar, Bool.or_eq_true] at hx
    rcases hx with h1 | h2
    · exact hasFreeVar_of_hasTy hl x h1
    · exact hasFreeVar_of_hasTy hr x h2
  | _, _, _, .letValue hv hp hb, x, hx => by
    simp only [hasFreeVar, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hx
    rcases hx with h1 | ⟨hnot, h2⟩
    · exact hasFreeVar_of_hasTy hv x h1
    · have hmem := hasFreeVar_of_hasTy hb x h2
      rw [List.map_append] at hmem
      rcases List.mem_append.mp hmem with hΔ | hΓ
      · rw [hp.dom_eq] at hΔ
        have := List.contains_iff_mem.mpr hΔ
        rw [this] at hnot; cases hnot
      · exact hΓ
  | _, _, _, .matchValue hs harms, x, hx => by
    simp only [hasFreeVar, Bool.or_eq_true] at hx
    rcases hx with h1 | h2
    · exact hasFreeVar_of_hasTy hs x h1
    · exact hasFreeVar_of_hasTyArms harms x h2

theorem hasFreeVar_of_hasTyList {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList sigs enums Γ xs ts → ∀ x, hasFreeVarList x xs = true → x ∈ Γ.map Prod.fst
  | _, _, _, .nil, _, hx => by simp [hasFreeVarList] at hx
  | _, _, _, .cons hd tl, x, hx => by
    simp only [hasFreeVarList, Bool.or_eq_true] at hx
    rcases hx with h1 | h2
    · exact hasFreeVar_of_hasTy hd x h1
    · exact hasFreeVar_of_hasTyList tl x h2

theorem hasFreeVar_of_hasTyArms {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} :
    ∀ {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms sigs enums Γ ts arms tb → ∀ x, hasFreeVarArms x arms = true → x ∈ Γ.map Prod.fst
  | _, _, _, _, .nil, _, hx => by simp [hasFreeVarArms] at hx
  | _, _, _, _, .cons hp hb tl, x, hx => by
    simp only [hasFreeVarArms, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hx
    rcases hx with ⟨hnot, h1⟩ | h2
    · have hmem := hasFreeVar_of_hasTy hb x h1
      rw [List.map_append] at hmem
      rcases List.mem_append.mp hmem with hΔ | hΓ
      · rw [hp.dom_eq] at hΔ
        have := List.contains_iff_mem.mpr hΔ
        rw [this] at hnot; cases hnot
      · exact hΓ
    · exact hasFreeVar_of_hasTyArms tl x h2

end

/-! ### Part 7C: `prefixPat` & `prefixExpr` Structural, Typing, & Evaluation Soundness -/

mutual

theorem patBoundVars_prefixPat (pfx : String) :
    ∀ p : Pat, patBoundVars (prefixPat pfx p) = (patBoundVars p).map (pfx ++ ·)
  | .bind _ => rfl
  | .tuple ps | .array ps | .construct _ _ ps | .constructAs _ _ _ ps | .record _ ps =>
    patListBoundVars_prefixPatList pfx ps
  | .wildcard | .literal _ | .global _ _ | .load _ | .orElse _ _ _ | .repeat _ _ => rfl

theorem patListBoundVars_prefixPatList (pfx : String) :
    ∀ ps : List Pat, patListBoundVars (prefixPatList pfx ps) = (patListBoundVars ps).map (pfx ++ ·)
  | [] => rfl
  | p :: ps => by
    simp only [prefixPatList, patListBoundVars, List.map_append,
      patBoundVars_prefixPat pfx p, patListBoundVars_prefixPatList pfx ps]

end

mutual

theorem isSimplePat_prefixPat (pfx : String) :
    ∀ p : Pat, isSimplePat (prefixPat pfx p) = isSimplePat p
  | .bind _ | .wildcard | .literal _ | .global _ _ | .load _ | .orElse _ _ _
  | .repeat _ _ | .record _ _ | .constructAs _ _ _ _ => rfl
  | .tuple ps | .array ps | .construct _ _ ps => isSimplePatList_prefixPatList pfx ps

theorem isSimplePatList_prefixPatList (pfx : String) :
    ∀ ps : List Pat, isSimplePatList (prefixPatList pfx ps) = isSimplePatList ps
  | [] => rfl
  | p :: ps => by
    simp only [prefixPatList, isSimplePatList, isSimplePat_prefixPat pfx p, isSimplePatList_prefixPatList pfx ps]

end

mutual

theorem hasBoundVar_prefixExpr (pfx : String) :
    ∀ (scope : List String) (e : Expr) (v : String),
      hasBoundVar v (prefixExpr pfx scope e) = true →
      ∃ u, v = pfx ++ u ∧ hasBoundVar u e = true
  | _, .literal _, _, h | _, .global _ _, _, h | _, .control _ _, _, h => by
    simp [prefixExpr, hasBoundVar] at h
  | scope, .var x, v, h => by
    simp only [prefixExpr] at h; split at h <;> simp [hasBoundVar] at h
  | scope, .tuple xs, v, h | scope, .array xs, v, h | scope, .construct _ _ _ xs, v, h
  | scope, .constructAs _ _ _ xs, v, h | scope, .record _ xs, v, h | scope, .update _ xs, v, h
  | scope, .builtin _ xs, v, h | scope, .call _ _ xs, v, h =>
    hasBoundVarList_prefixExprList pfx scope xs v h
  | scope, .repeat x _, v, h | scope, .index x _, v, h | scope, .slice x _ _, v, h
  | scope, .member x _, v, h | scope, .project x _, v, h | scope, .store x, v, h
  | scope, .load x, v, h | scope, .hint _ x _, v, h | scope, .neg x, v, h =>
    hasBoundVar_prefixExpr pfx scope x v h
  | scope, .binary _ l r, v, h => by
    simp only [prefixExpr, hasBoundVar, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope l v h1
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope r v h2
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
  | scope, .letValue p x b, v, h => by
    simp only [prefixExpr, hasBoundVar, patBoundVars_prefixPat, Bool.or_eq_true] at h
    rcases h with (h1 | h2) | h3
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h1)
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope x v h2
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx (patBoundVars p ++ scope) b v h3
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
  | scope, .matchValue s arms, v, h => by
    simp only [prefixExpr, hasBoundVar, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope s v h1
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVarArms_prefixArms pfx scope arms v h2
      exact ⟨u, rfl, by simp [hasBoundVar, hu]⟩
termination_by _ e _ _ => sizeOf e

theorem hasBoundVarList_prefixExprList (pfx : String) :
    ∀ (scope : List String) (xs : List Expr) (v : String),
      hasBoundVarList v (prefixExprList pfx scope xs) = true →
      ∃ u, v = pfx ++ u ∧ hasBoundVarList u xs = true
  | _, [], _, h => by simp [prefixExprList, hasBoundVarList] at h
  | scope, x :: xs, v, h => by
    simp only [prefixExprList, hasBoundVarList, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope x v h1
      exact ⟨u, rfl, by simp [hasBoundVarList, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVarList_prefixExprList pfx scope xs v h2
      exact ⟨u, rfl, by simp [hasBoundVarList, hu]⟩
termination_by _ xs _ _ => sizeOf xs

theorem hasBoundVarArms_prefixArms (pfx : String) :
    ∀ (scope : List String) (arms : List (Pat × Expr)) (v : String),
      hasBoundVarArms v (prefixArms pfx scope arms) = true →
      ∃ u, v = pfx ++ u ∧ hasBoundVarArms u arms = true
  | _, [], _, h => by simp [prefixArms, hasBoundVarArms] at h
  | scope, (p, b) :: rest, v, h => by
    simp only [prefixArms, hasBoundVarArms, patBoundVars_prefixPat, Bool.or_eq_true] at h
    rcases h with (h1 | h2) | h3
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h1)
      exact ⟨u, rfl, by simp [hasBoundVarArms, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx (patBoundVars p ++ scope) b v h2
      exact ⟨u, rfl, by simp [hasBoundVarArms, hu]⟩
    · obtain ⟨u, rfl, hu⟩ := hasBoundVarArms_prefixArms pfx scope rest v h3
      exact ⟨u, rfl, by simp [hasBoundVarArms, hu]⟩
termination_by _ arms _ _ => sizeOf arms

end

mutual

theorem hasFreeVar_prefixExpr_closed (pfx : String) :
    ∀ (scope : List String) (e : Expr),
      (∀ u, hasFreeVar u e = true → u ∈ scope) →
      ∀ v, hasFreeVar v (prefixExpr pfx scope e) = true →
        ∃ u, u ∈ scope ∧ v = pfx ++ u ∧ hasFreeVar u e = true
  | _, .literal _, _, _, h | _, .global _ _, _, _, h | _, .control _ _, _, _, h => by
    simp [prefixExpr, hasFreeVar] at h
  | scope, .var x, hcl, v, h => by
    have hxMem : x ∈ scope := hcl x (by simp [hasFreeVar])
    have hxC : scope.contains x = true := List.contains_iff_mem.mpr hxMem
    simp only [prefixExpr, hxC, ↓reduceIte, hasFreeVar, beq_iff_eq] at h
    exact ⟨x, hxMem, h.symm, by simp [hasFreeVar]⟩
  | scope, .tuple xs, hcl, v, h | scope, .array xs, hcl, v, h
  | scope, .construct _ _ _ xs, hcl, v, h | scope, .constructAs _ _ _ xs, hcl, v, h
  | scope, .record _ xs, hcl, v, h | scope, .update _ xs, hcl, v, h
  | scope, .builtin _ xs, hcl, v, h | scope, .call _ _ xs, hcl, v, h =>
    hasFreeVarList_prefixExprList_closed pfx scope xs hcl v h
  | scope, .repeat x _, hcl, v, h | scope, .index x _, hcl, v, h | scope, .slice x _ _, hcl, v, h
  | scope, .member x _, hcl, v, h | scope, .project x _, hcl, v, h | scope, .store x, hcl, v, h
  | scope, .load x, hcl, v, h | scope, .hint _ x _, hcl, v, h | scope, .neg x, hcl, v, h =>
    hasFreeVar_prefixExpr_closed pfx scope x hcl v h
  | scope, .binary _ l r, hcl, v, h => by
    simp only [prefixExpr, hasFreeVar, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx scope l
        (fun w hw => hcl w (by simp [hasFreeVar, hw])) v h1
      exact ⟨u, hu, rfl, by simp [hasFreeVar, hf]⟩
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx scope r
        (fun w hw => hcl w (by simp [hasFreeVar, hw])) v h2
      exact ⟨u, hu, rfl, by simp [hasFreeVar, hf]⟩
  | scope, .letValue p x b, hcl, v, h => by
    simp only [prefixExpr, hasFreeVar, patBoundVars_prefixPat, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at h
    rcases h with h1 | ⟨hnot, h2⟩
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx scope x
        (fun w hw => hcl w (by simp [hasFreeVar, hw])) v h1
      exact ⟨u, hu, rfl, by simp [hasFreeVar, hf]⟩
    · have hclB : ∀ w, hasFreeVar w b = true → w ∈ patBoundVars p ++ scope := by
        intro w hw
        by_cases hp : w ∈ patBoundVars p
        · exact List.mem_append_left _ hp
        · exact List.mem_append_right _ (hcl w (by simp [hasFreeVar, hp, hw]))
      obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx (patBoundVars p ++ scope) b hclB v h2
      have hnotP : u ∉ patBoundVars p := by
        intro hmem
        have : ((patBoundVars p).map (pfx ++ ·)).contains (pfx ++ u) = true :=
          List.contains_iff_mem.mpr (List.mem_map.mpr ⟨u, hmem, rfl⟩)
        rw [this] at hnot; cases hnot
      have huScope : u ∈ scope := (List.mem_append.mp hu).resolve_left hnotP
      exact ⟨u, huScope, rfl, by simp [hasFreeVar, hnotP, hf]⟩
  | scope, .matchValue s arms, hcl, v, h => by
    simp only [prefixExpr, hasFreeVar, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx scope s
        (fun w hw => hcl w (by simp [hasFreeVar, hw])) v h1
      exact ⟨u, hu, rfl, by simp [hasFreeVar, hf]⟩
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVarArms_prefixArms_closed pfx scope arms
        (fun w hw => hcl w (by simp [hasFreeVar, hw])) v h2
      exact ⟨u, hu, rfl, by simp [hasFreeVar, hf]⟩
termination_by _ e _ _ _ => sizeOf e

theorem hasFreeVarList_prefixExprList_closed (pfx : String) :
    ∀ (scope : List String) (xs : List Expr),
      (∀ u, hasFreeVarList u xs = true → u ∈ scope) →
      ∀ v, hasFreeVarList v (prefixExprList pfx scope xs) = true →
        ∃ u, u ∈ scope ∧ v = pfx ++ u ∧ hasFreeVarList u xs = true
  | _, [], _, _, h => by simp [prefixExprList, hasFreeVarList] at h
  | scope, x :: xs, hcl, v, h => by
    simp only [prefixExprList, hasFreeVarList, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx scope x
        (fun w hw => hcl w (by simp [hasFreeVarList, hw])) v h1
      exact ⟨u, hu, rfl, by simp [hasFreeVarList, hf]⟩
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVarList_prefixExprList_closed pfx scope xs
        (fun w hw => hcl w (by simp [hasFreeVarList, hw])) v h2
      exact ⟨u, hu, rfl, by simp [hasFreeVarList, hf]⟩
termination_by _ xs _ _ _ => sizeOf xs

theorem hasFreeVarArms_prefixArms_closed (pfx : String) :
    ∀ (scope : List String) (arms : List (Pat × Expr)),
      (∀ u, hasFreeVarArms u arms = true → u ∈ scope) →
      ∀ v, hasFreeVarArms v (prefixArms pfx scope arms) = true →
        ∃ u, u ∈ scope ∧ v = pfx ++ u ∧ hasFreeVarArms u arms = true
  | _, [], _, _, h => by simp [prefixArms, hasFreeVarArms] at h
  | scope, (p, b) :: rest, hcl, v, h => by
    simp only [prefixArms, hasFreeVarArms, patBoundVars_prefixPat, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at h
    rcases h with ⟨hnot, h1⟩ | h2
    · have hclB : ∀ w, hasFreeVar w b = true → w ∈ patBoundVars p ++ scope := by
        intro w hw
        by_cases hp : w ∈ patBoundVars p
        · exact List.mem_append_left _ hp
        · exact List.mem_append_right _ (hcl w (by simp [hasFreeVarArms, hp, hw]))
      obtain ⟨u, hu, rfl, hf⟩ := hasFreeVar_prefixExpr_closed pfx (patBoundVars p ++ scope) b hclB v h1
      have hnotP : u ∉ patBoundVars p := by
        intro hmem
        have : ((patBoundVars p).map (pfx ++ ·)).contains (pfx ++ u) = true :=
          List.contains_iff_mem.mpr (List.mem_map.mpr ⟨u, hmem, rfl⟩)
        rw [this] at hnot; cases hnot
      have huScope : u ∈ scope := (List.mem_append.mp hu).resolve_left hnotP
      exact ⟨u, huScope, rfl, by simp [hasFreeVarArms, hnotP, hf]⟩
    · obtain ⟨u, hu, rfl, hf⟩ := hasFreeVarArms_prefixArms_closed pfx scope rest
        (fun w hw => hcl w (by simp [hasFreeVarArms, hw])) v h2
      exact ⟨u, hu, rfl, by simp [hasFreeVarArms, hf]⟩
termination_by _ arms _ _ _ => sizeOf arms

end

mutual

theorem noLetShadow_prefixExpr (pfx : String) (outer : List String) :
    ∀ (scope : List String) {e : Expr},
      NoLetShadow scope e →
      (∀ u, hasBoundVar u e = true → pfx ++ u ∉ outer) →
      NoLetShadow (scope.map (pfx ++ ·) ++ outer) (prefixExpr pfx scope e)
  | _, .literal _, _, _ | _, .global _ _, _, _ | _, .control _ _, _, _ => trivial
  | scope, .var x, _, _ => by simp only [prefixExpr]; split <;> trivial
  | scope, .tuple xs, h, ho | scope, .array xs, h, ho | scope, .construct _ _ _ xs, h, ho
  | scope, .constructAs _ _ _ xs, h, ho | scope, .record _ xs, h, ho | scope, .update _ xs, h, ho
  | scope, .builtin _ xs, h, ho | scope, .call _ _ xs, h, ho =>
    noLetShadowList_prefixExprList pfx outer scope h ho
  | scope, .repeat x _, h, ho | scope, .index x _, h, ho | scope, .slice x _ _, h, ho
  | scope, .member x _, h, ho | scope, .project x _, h, ho | scope, .store x, h, ho
  | scope, .load x, h, ho | scope, .hint _ x _, h, ho | scope, .neg x, h, ho =>
    noLetShadow_prefixExpr pfx outer scope (e := x) h ho
  | scope, .binary _ l r, ⟨hdisj, hl, hr⟩, ho => by
    simp only [prefixExpr, NoLetShadow]
    refine ⟨fun v hv => ?_,
      noLetShadow_prefixExpr pfx outer scope hl (fun u hu => ho u (by simp [hasBoundVar, hu])),
      noLetShadow_prefixExpr pfx outer scope hr (fun u hu => ho u (by simp [hasBoundVar, hu]))⟩
    obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope l v hv
    cases hrb : hasBoundVar (pfx ++ u) (prefixExpr pfx scope r) with
    | false => rfl
    | true =>
      obtain ⟨u', heq, hu'⟩ := hasBoundVar_prefixExpr pfx scope r _ hrb
      have := string_append_left_inj heq; subst this
      rw [hdisj u hu] at hu'; cases hu'
  | scope, .letValue p x b, ⟨hp, hdisj, hx, hb⟩, ho => by
    simp only [prefixExpr, NoLetShadow, patBoundVars_prefixPat]
    refine ⟨fun v hvp hmem => ?_, fun v hv => ?_,
      noLetShadow_prefixExpr pfx outer scope hx (fun u hu => ho u (by simp [hasBoundVar, hu])), ?_⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hvp
      rcases List.mem_append.mp hmem with h1 | h2
      · obtain ⟨u', hu', heq⟩ := List.mem_map.mp h1
        have := string_append_left_inj heq; subst this
        exact hp u' hu hu'
      · exact ho u (by simp [hasBoundVar, hu]) h2
    · obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope x v hv
      obtain ⟨hnp, hnb⟩ := hdisj u hu
      refine ⟨fun hmem => ?_, ?_⟩
      · obtain ⟨u', hu', heq⟩ := List.mem_map.mp hmem
        have := string_append_left_inj heq; subst this
        exact hnp hu'
      · cases hbb : hasBoundVar (pfx ++ u) (prefixExpr pfx (patBoundVars p ++ scope) b) with
        | false => rfl
        | true =>
          obtain ⟨u', heq, hu'⟩ := hasBoundVar_prefixExpr pfx (patBoundVars p ++ scope) b _ hbb
          have := string_append_left_inj heq; subst this
          rw [hnb] at hu'; cases hu'
    · rw [← List.append_assoc, ← List.map_append]
      exact noLetShadow_prefixExpr pfx outer (patBoundVars p ++ scope) hb
        (fun u hu => ho u (by simp [hasBoundVar, hu]))
  | scope, .matchValue s arms, ⟨hs, harms⟩, ho => by
    simp only [prefixExpr, NoLetShadow]
    exact ⟨noLetShadow_prefixExpr pfx outer scope hs (fun u hu => ho u (by simp [hasBoundVar, hu])),
      noLetShadowArms_prefixArms pfx outer scope harms (fun u hu => ho u (by simp [hasBoundVar, hu]))⟩
termination_by _ e _ _ => sizeOf e

theorem noLetShadowList_prefixExprList (pfx : String) (outer : List String) :
    ∀ (scope : List String) {xs : List Expr},
      NoLetShadowList scope xs →
      (∀ u, hasBoundVarList u xs = true → pfx ++ u ∉ outer) →
      NoLetShadowList (scope.map (pfx ++ ·) ++ outer) (prefixExprList pfx scope xs)
  | _, [], _, _ => trivial
  | scope, x :: xs, ⟨hdisj, hx, hxs⟩, ho => by
    simp only [prefixExprList, NoLetShadowList]
    refine ⟨fun v hv => ?_,
      noLetShadow_prefixExpr pfx outer scope hx (fun u hu => ho u (by simp [hasBoundVarList, hu])),
      noLetShadowList_prefixExprList pfx outer scope hxs (fun u hu => ho u (by simp [hasBoundVarList, hu]))⟩
    obtain ⟨u, rfl, hu⟩ := hasBoundVar_prefixExpr pfx scope x v hv
    cases hrb : hasBoundVarList (pfx ++ u) (prefixExprList pfx scope xs) with
    | false => rfl
    | true =>
      obtain ⟨u', heq, hu'⟩ := hasBoundVarList_prefixExprList pfx scope xs _ hrb
      have := string_append_left_inj heq; subst this
      rw [hdisj u hu] at hu'; cases hu'
termination_by _ xs _ _ => sizeOf xs

theorem noLetShadowArms_prefixArms (pfx : String) (outer : List String) :
    ∀ (scope : List String) {arms : List (Pat × Expr)},
      NoLetShadowArms scope arms →
      (∀ u, hasBoundVarArms u arms = true → pfx ++ u ∉ outer) →
      NoLetShadowArms (scope.map (pfx ++ ·) ++ outer) (prefixArms pfx scope arms)
  | _, [], _, _ => trivial
  | scope, (p, b) :: rest, ⟨hp, hb, hrest⟩, ho => by
    simp only [prefixArms, NoLetShadowArms, patBoundVars_prefixPat]
    refine ⟨fun v hvp hmem => ?_, ?_,
      noLetShadowArms_prefixArms pfx outer scope hrest (fun u hu => ho u (by simp [hasBoundVarArms, hu]))⟩
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hvp
      rcases List.mem_append.mp hmem with h1 | h2
      · obtain ⟨u', hu', heq⟩ := List.mem_map.mp h1
        have := string_append_left_inj heq; subst this
        exact hp u' hu hu'
      · exact ho u (by simp [hasBoundVarArms, hu]) h2
    · rw [← List.append_assoc, ← List.map_append]
      exact noLetShadow_prefixExpr pfx outer (patBoundVars p ++ scope) hb
        (fun u hu => ho u (by simp [hasBoundVarArms, hu]))
termination_by _ arms _ _ => sizeOf arms

end

mutual

theorem allLitsLt_prefixExpr (bound : Nat) (pfx : String) :
    ∀ (scope : List String) (e : Expr),
      allLitsLt bound (prefixExpr pfx scope e) = allLitsLt bound e
  | _, .literal _ | _, .global _ _ | _, .control _ _ => rfl
  | scope, .var x => by simp only [prefixExpr]; split <;> rfl
  | scope, .tuple xs | scope, .array xs | scope, .construct _ _ _ xs | scope, .constructAs _ _ _ xs
  | scope, .record _ xs | scope, .update _ xs | scope, .builtin _ xs | scope, .call _ _ xs =>
    allLitsLtList_prefixExprList bound pfx scope xs
  | scope, .repeat x _ | scope, .index x _ | scope, .slice x _ _ | scope, .member x _
  | scope, .project x _ | scope, .store x | scope, .load x | scope, .hint _ x _ | scope, .neg x =>
    allLitsLt_prefixExpr bound pfx scope x
  | scope, .binary _ l r => by
    simp only [prefixExpr, allLitsLt, allLitsLt_prefixExpr bound pfx scope l,
      allLitsLt_prefixExpr bound pfx scope r]
  | scope, .letValue p v b => by
    simp only [prefixExpr, allLitsLt, allLitsLt_prefixExpr bound pfx scope v,
      allLitsLt_prefixExpr bound pfx (patBoundVars p ++ scope) b]
  | scope, .matchValue s arms => by
    simp only [prefixExpr, allLitsLt, allLitsLt_prefixExpr bound pfx scope s,
      allLitsLtArms_prefixArms bound pfx scope arms]
termination_by _ e => sizeOf e

theorem allLitsLtList_prefixExprList (bound : Nat) (pfx : String) :
    ∀ (scope : List String) (xs : List Expr),
      allLitsLtList bound (prefixExprList pfx scope xs) = allLitsLtList bound xs
  | _, [] => rfl
  | scope, x :: xs => by
    simp only [prefixExprList, allLitsLtList, allLitsLt_prefixExpr bound pfx scope x,
      allLitsLtList_prefixExprList bound pfx scope xs]
termination_by _ xs => sizeOf xs

theorem allLitsLtArms_prefixArms (bound : Nat) (pfx : String) :
    ∀ (scope : List String) (arms : List (Pat × Expr)),
      allLitsLtArms bound (prefixArms pfx scope arms) = allLitsLtArms bound arms
  | _, [] => rfl
  | scope, (p, b) :: rest => by
    simp only [prefixArms, allLitsLtArms,
      allLitsLt_prefixExpr bound pfx (patBoundVars p ++ scope) b,
      allLitsLtArms_prefixArms bound pfx scope rest]
termination_by _ arms => sizeOf arms

end

mutual

theorem literalsBounded_prefixExpr (pfx : String) :
    ∀ (scope : List String) (e : Expr),
      literalsBounded (prefixExpr pfx scope e) = literalsBounded e
  | _, .literal _ | _, .global _ _ | _, .control _ _ => rfl
  | scope, .var x => by simp only [prefixExpr]; split <;> rfl
  | scope, .tuple xs | scope, .array xs | scope, .construct _ _ _ xs | scope, .constructAs _ _ _ xs
  | scope, .record _ xs | scope, .update _ xs | scope, .builtin _ xs =>
    literalsBoundedList_prefixExprList pfx scope xs
  | scope, .repeat x _ | scope, .index x _ | scope, .slice x _ _ | scope, .member x _
  | scope, .project x _ | scope, .store x | scope, .load x | scope, .hint _ x _ | scope, .neg x =>
    literalsBounded_prefixExpr pfx scope x
  | scope, .binary _ l r => by
    simp only [prefixExpr, literalsBounded, literalsBounded_prefixExpr pfx scope l,
      literalsBounded_prefixExpr pfx scope r]
  | scope, .letValue p v b => by
    simp only [prefixExpr, literalsBounded, literalsBounded_prefixExpr pfx scope v,
      literalsBounded_prefixExpr pfx (patBoundVars p ++ scope) b]
  | scope, .matchValue s arms => by
    simp only [prefixExpr, literalsBounded, literalsBounded_prefixExpr pfx scope s,
      literalsBoundedArms_prefixArms pfx scope arms]
  | scope, .call nm targs xs => by
    cases targs with
    | none => exact literalsBoundedList_prefixExprList pfx scope xs
    | some ts =>
      cases ts with
      | cons _ _ => exact literalsBoundedList_prefixExprList pfx scope xs
      | nil =>
        cases xs with
        | nil => rfl
        | cons x rest =>
          cases rest with
          | cons y rest2 =>
            simp only [prefixExpr, prefixExprList, literalsBounded, literalsBoundedList,
              literalsBounded_prefixExpr pfx scope x, literalsBounded_prefixExpr pfx scope y,
              literalsBoundedList_prefixExprList pfx scope rest2]
          | nil =>
            simp only [prefixExpr, prefixExprList, literalsBounded,
              allLitsLt_prefixExpr _ pfx scope x, literalsBounded_prefixExpr pfx scope x]
termination_by _ e => sizeOf e
decreasing_by
  all_goals try simp_wf
  all_goals omega

theorem literalsBoundedList_prefixExprList (pfx : String) :
    ∀ (scope : List String) (xs : List Expr),
      literalsBoundedList (prefixExprList pfx scope xs) = literalsBoundedList xs
  | _, [] => rfl
  | scope, x :: xs => by
    simp only [prefixExprList, literalsBoundedList, literalsBounded_prefixExpr pfx scope x,
      literalsBoundedList_prefixExprList pfx scope xs]
termination_by _ xs => sizeOf xs

theorem literalsBoundedArms_prefixArms (pfx : String) :
    ∀ (scope : List String) (arms : List (Pat × Expr)),
      literalsBoundedArms (prefixArms pfx scope arms) = literalsBoundedArms arms
  | _, [] => rfl
  | scope, (p, b) :: rest => by
    simp only [prefixArms, literalsBoundedArms,
      literalsBounded_prefixExpr pfx (patBoundVars p ++ scope) b,
      literalsBoundedArms_prefixArms pfx scope rest]
termination_by _ arms => sizeOf arms

end

mutual

theorem noInlinableCalls_prefixExpr (pfx : String) :
    ∀ (scope : List String) (e : Expr),
      noInlinableCalls (prefixExpr pfx scope e) = noInlinableCalls e
  | _, .literal _ | _, .global _ _ | _, .control _ _ => rfl
  | scope, .var x => by simp only [prefixExpr]; split <;> rfl
  | scope, .tuple xs | scope, .array xs | scope, .construct _ _ _ xs | scope, .constructAs _ _ _ xs
  | scope, .record _ xs | scope, .update _ xs | scope, .builtin _ xs =>
    noInlinableCallsList_prefixExprList pfx scope xs
  | scope, .call _ _ xs => by
    simp only [prefixExpr, noInlinableCalls, noInlinableCallsList_prefixExprList pfx scope xs]
  | scope, .repeat x _ | scope, .index x _ | scope, .slice x _ _ | scope, .member x _
  | scope, .project x _ | scope, .store x | scope, .load x | scope, .hint _ x _ | scope, .neg x =>
    noInlinableCalls_prefixExpr pfx scope x
  | scope, .binary _ l r => by
    simp only [prefixExpr, noInlinableCalls, noInlinableCalls_prefixExpr pfx scope l,
      noInlinableCalls_prefixExpr pfx scope r]
  | scope, .letValue p v b => by
    simp only [prefixExpr, noInlinableCalls, noInlinableCalls_prefixExpr pfx scope v,
      noInlinableCalls_prefixExpr pfx (patBoundVars p ++ scope) b]
  | scope, .matchValue s arms => by
    simp only [prefixExpr, noInlinableCalls, noInlinableCalls_prefixExpr pfx scope s,
      noInlinableCallsArms_prefixArms pfx scope arms]
termination_by _ e => sizeOf e

theorem noInlinableCallsList_prefixExprList (pfx : String) :
    ∀ (scope : List String) (xs : List Expr),
      noInlinableCallsList (prefixExprList pfx scope xs) = noInlinableCallsList xs
  | _, [] => rfl
  | scope, x :: xs => by
    simp only [prefixExprList, noInlinableCallsList, noInlinableCalls_prefixExpr pfx scope x,
      noInlinableCallsList_prefixExprList pfx scope xs]
termination_by _ xs => sizeOf xs

theorem noInlinableCallsArms_prefixArms (pfx : String) :
    ∀ (scope : List String) (arms : List (Pat × Expr)),
      noInlinableCallsArms (prefixArms pfx scope arms) = noInlinableCallsArms arms
  | _, [] => rfl
  | scope, (p, b) :: rest => by
    simp only [prefixArms, noInlinableCallsArms,
      noInlinableCalls_prefixExpr pfx (patBoundVars p ++ scope) b,
      noInlinableCallsArms_prefixArms pfx scope rest]
termination_by _ arms => sizeOf arms

end

mutual

theorem noInlinableInBoundedCalls_prefixExpr (pfx : String) :
    ∀ (scope : List String) (e : Expr),
      noInlinableInBoundedCalls (prefixExpr pfx scope e) = noInlinableInBoundedCalls e
  | _, .literal _ | _, .global _ _ | _, .control _ _ => rfl
  | scope, .var x => by simp only [prefixExpr]; split <;> rfl
  | scope, .tuple xs | scope, .array xs | scope, .construct _ _ _ xs | scope, .constructAs _ _ _ xs
  | scope, .record _ xs | scope, .update _ xs | scope, .builtin _ xs =>
    noInlinableInBoundedCallsList_prefixExprList pfx scope xs
  | scope, .repeat x _ | scope, .index x _ | scope, .slice x _ _ | scope, .member x _
  | scope, .project x _ | scope, .store x | scope, .load x | scope, .hint _ x _ | scope, .neg x =>
    noInlinableInBoundedCalls_prefixExpr pfx scope x
  | scope, .binary _ l r => by
    simp only [prefixExpr, noInlinableInBoundedCalls, noInlinableInBoundedCalls_prefixExpr pfx scope l,
      noInlinableInBoundedCalls_prefixExpr pfx scope r]
  | scope, .letValue p v b => by
    simp only [prefixExpr, noInlinableInBoundedCalls, noInlinableInBoundedCalls_prefixExpr pfx scope v,
      noInlinableInBoundedCalls_prefixExpr pfx (patBoundVars p ++ scope) b]
  | scope, .matchValue s arms => by
    simp only [prefixExpr, noInlinableInBoundedCalls, noInlinableInBoundedCalls_prefixExpr pfx scope s,
      noInlinableInBoundedCallsArms_prefixArms pfx scope arms]
  | scope, .call nm targs xs => by
    cases targs with
    | none => exact noInlinableInBoundedCallsList_prefixExprList pfx scope xs
    | some ts =>
      cases ts with
      | cons _ _ => exact noInlinableInBoundedCallsList_prefixExprList pfx scope xs
      | nil =>
        cases xs with
        | nil => rfl
        | cons x rest =>
          cases rest with
          | cons y rest2 =>
            simp only [prefixExpr, prefixExprList, noInlinableInBoundedCalls, noInlinableInBoundedCallsList,
              noInlinableInBoundedCalls_prefixExpr pfx scope x, noInlinableInBoundedCalls_prefixExpr pfx scope y,
              noInlinableInBoundedCallsList_prefixExprList pfx scope rest2]
          | nil =>
            simp only [prefixExpr, prefixExprList, noInlinableInBoundedCalls,
              noInlinableCalls_prefixExpr pfx scope x, noInlinableInBoundedCalls_prefixExpr pfx scope x]
termination_by _ e => sizeOf e
decreasing_by
  all_goals try simp_wf
  all_goals omega

theorem noInlinableInBoundedCallsList_prefixExprList (pfx : String) :
    ∀ (scope : List String) (xs : List Expr),
      noInlinableInBoundedCallsList (prefixExprList pfx scope xs) = noInlinableInBoundedCallsList xs
  | _, [] => rfl
  | scope, x :: xs => by
    simp only [prefixExprList, noInlinableInBoundedCallsList,
      noInlinableInBoundedCalls_prefixExpr pfx scope x,
      noInlinableInBoundedCallsList_prefixExprList pfx scope xs]
termination_by _ xs => sizeOf xs

theorem noInlinableInBoundedCallsArms_prefixArms (pfx : String) :
    ∀ (scope : List String) (arms : List (Pat × Expr)),
      noInlinableInBoundedCallsArms (prefixArms pfx scope arms) = noInlinableInBoundedCallsArms arms
  | _, [] => rfl
  | scope, (p, b) :: rest => by
    simp only [prefixArms, noInlinableInBoundedCallsArms,
      noInlinableInBoundedCalls_prefixExpr pfx (patBoundVars p ++ scope) b,
      noInlinableInBoundedCallsArms_prefixArms pfx scope rest]
termination_by _ arms => sizeOf arms

end

theorem prefixPatList_length (pfx : String) :
    ∀ ps : List Pat, (prefixPatList pfx ps).length = ps.length
  | [] => rfl
  | _ :: ps => congrArg Nat.succ (prefixPatList_length pfx ps)

theorem prefixExprList_length (pfx : String) (scope : List String) :
    ∀ xs : List Expr, (prefixExprList pfx scope xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (prefixExprList_length pfx scope xs)

mutual

theorem patHasTy_prefixPat {enums : List Aiur.Generic.EnumDecl} (pfx : String) :
    ∀ {p : Pat} {t : Lower.Ty} {Δ : TyEnv},
      PatHasTy enums p t Δ →
      PatHasTy enums (prefixPat pfx p) t (Δ.map fun q => (pfx ++ q.1, q.2))
  | _, _, _, .wildcard => .wildcard
  | _, _, _, .literal => .literal
  | _, _, _, .bind => .bind
  | _, _, _, .tuple items => .tuple (patListHasTy_prefixPatList pfx items)
  | _, _, _, .array items =>
    .array (by rw [prefixPatList_length]; exact patListHasTy_prefixPatList pfx items)
  | _, _, _, .construct hne hctor items =>
    .construct hne hctor (patListHasTy_prefixPatList pfx items)

theorem patListHasTy_prefixPatList {enums : List Aiur.Generic.EnumDecl} (pfx : String) :
    ∀ {ps : List Pat} {ts : List Lower.Ty} {Δ : TyEnv},
      PatListHasTy enums ps ts Δ →
      PatListHasTy enums (prefixPatList pfx ps) ts (Δ.map fun q => (pfx ++ q.1, q.2))
  | _, _, _, .nil => .nil
  | _, _, _, .cons hd tl => by
    rw [List.map_append]
    exact .cons (patHasTy_prefixPat pfx hd) (patListHasTy_prefixPatList pfx tl)

end

private theorem lookup_map_prefix {α : Type} (pfx : String) :
    ∀ (Δ : List (String × α)) (x : String),
      (Δ.map fun q => (pfx ++ q.1, q.2)).lookup (pfx ++ x) = Δ.lookup x
  | [], _ => rfl
  | (k, v) :: tl, x => by
    simp only [List.map_cons, List.lookup]
    by_cases hx : x = k
    · subst hx; simp
    · have hne : pfx ++ x ≠ pfx ++ k := fun heq => hx (string_append_left_inj heq)
      simp only [beq_false_of_ne hx, beq_false_of_ne hne]
      exact lookup_map_prefix pfx tl x

private theorem lookup_append_map_prefix {α : Type} (pfx : String)
    {Δ Γ1 Γ2 : List (String × α)} {x : String}
    (hnot : x ∉ Δ.map Prod.fst → Γ1.lookup x = Γ2.lookup (pfx ++ x)) :
    (Δ ++ Γ1).lookup x = ((Δ.map fun q => (pfx ++ q.1, q.2)) ++ Γ2).lookup (pfx ++ x) := by
  induction Δ with
  | nil => exact hnot (by simp)
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.cons_append, List.lookup]
    by_cases hx : x = k
    · subst hx; simp
    · have hne : pfx ++ x ≠ pfx ++ k := fun heq => hx (string_append_left_inj heq)
      simp only [beq_false_of_ne hx, beq_false_of_ne hne]
      exact ih fun hn => hnot (by simp [hx, hn])

mutual

/-- Typing preservation for `prefixExpr` on closed subexpressions (`∀ x, hasFreeVar x e = true → x ∈ scope`). -/
theorem hasTy_prefixExpr {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} (pfx : String) :
    ∀ (scope : List String) {ΓOrig ΓPref : TyEnv} {e : Expr} {t : Lower.Ty},
      HasTy sigs enums ΓOrig e t →
      (∀ x, hasFreeVar x e = true → x ∈ scope ∧ ΓOrig.lookup x = ΓPref.lookup (pfx ++ x)) →
      HasTy sigs enums ΓPref (prefixExpr pfx scope e) t
  | _, _, _, _, _, .literal, _ => .literal
  | scope, _, _, _, _, .var (x := x) hl, hag => by
    obtain ⟨hmem, heq⟩ := hag x (by simp [hasFreeVar])
    have hc : scope.contains x = true := List.contains_iff_mem.mpr hmem
    simp only [prefixExpr, hc, ↓reduceIte]
    exact .var (heq ▸ hl)
  | scope, _, _, _, _, .tuple items, hag => .tuple (hasTyList_prefixExprList pfx scope items hag)
  | scope, _, _, _, _, .array hlen items, hag =>
    .array (by rw [prefixExprList_length]; exact hlen) (hasTyList_prefixExprList pfx scope items hag)
  | scope, _, _, _, _, .repeat hx, hag => .repeat (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .index hx, hag => .index (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .project hx hget, hag => .project (hasTy_prefixExpr pfx scope hx hag) hget
  | scope, _, _, _, _, .slice hnot hx, hag => .slice hnot (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .construct h1 h2 h3 h4 hctor items, hag =>
    .construct h1 h2 h3 h4 hctor (hasTyList_prefixExprList pfx scope items hag)
  | scope, _, _, _, _, .builtin items, hag => .builtin (hasTyList_prefixExprList pfx scope items hag)
  | scope, _, _, _, _, .store hx, hag => .store (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .load hx, hag => .load (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .hint hfo hx, hag => .hint hfo (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .neg hx, hag => .neg (hasTy_prefixExpr pfx scope hx hag)
  | scope, _, _, _, _, .binary hl hr, hag =>
    .binary
      (hasTy_prefixExpr pfx scope hl fun x hx => hag x (by simp [hasFreeVar, hx]))
      (hasTy_prefixExpr pfx scope hr fun x hx => hag x (by simp [hasFreeVar, hx]))
  | scope, _, _, _, _, .call hsig items, hag => .call hsig (hasTyList_prefixExprList pfx scope items hag)
  | scope, _, _, .letValue p _ _, _, .letValue hx hp hb, hag => by
    refine .letValue
      (hasTy_prefixExpr pfx scope hx fun x hfx => hag x (by simp [hasFreeVar, hfx]))
      (patHasTy_prefixPat pfx hp)
      (hasTy_prefixExpr pfx (patBoundVars p ++ scope) hb fun x hfb => ?_)
    refine ⟨?_, lookup_append_map_prefix pfx fun hnot => ?_⟩
    · by_cases hmem : x ∈ patBoundVars p
      · exact List.mem_append_left _ hmem
      · exact List.mem_append_right _ (hag x (by simp [hasFreeVar, hmem, hfb])).1
    · rw [hp.dom_eq] at hnot
      exact (hag x (by simp [hasFreeVar, hnot, hfb])).2
  | scope, _, _, _, _, .matchValue hs harms, hag =>
    .matchValue
      (hasTy_prefixExpr pfx scope hs fun x hfs => hag x (by simp [hasFreeVar, hfs]))
      (hasTyArms_prefixArms pfx scope harms fun x hfa => hag x (by simp [hasFreeVar, hfa]))

theorem hasTyList_prefixExprList {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} (pfx : String) :
    ∀ (scope : List String) {ΓOrig ΓPref : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      HasTyList sigs enums ΓOrig xs ts →
      (∀ x, hasFreeVarList x xs = true → x ∈ scope ∧ ΓOrig.lookup x = ΓPref.lookup (pfx ++ x)) →
      HasTyList sigs enums ΓPref (prefixExprList pfx scope xs) ts
  | _, _, _, _, _, .nil, _ => .nil
  | scope, _, _, _, _, .cons hd tl, hag =>
    .cons
      (hasTy_prefixExpr pfx scope hd fun x hx => hag x (by simp [hasFreeVarList, hx]))
      (hasTyList_prefixExprList pfx scope tl fun x hx => hag x (by simp [hasFreeVarList, hx]))

theorem hasTyArms_prefixArms {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} (pfx : String) :
    ∀ (scope : List String) {ΓOrig ΓPref : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      HasTyArms sigs enums ΓOrig ts arms tb →
      (∀ x, hasFreeVarArms x arms = true → x ∈ scope ∧ ΓOrig.lookup x = ΓPref.lookup (pfx ++ x)) →
      HasTyArms sigs enums ΓPref ts (prefixArms pfx scope arms) tb
  | _, _, _, _, _, _, .nil, _ => .nil
  | scope, _, _, _, _, (p, _) :: _, .cons hp hb tl, hag => by
    refine .cons (patHasTy_prefixPat pfx hp)
      (hasTy_prefixExpr pfx (patBoundVars p ++ scope) hb fun x hfb => ?_)
      (hasTyArms_prefixArms pfx scope tl fun x hfa => hag x (by simp [hasFreeVarArms, hfa]))
    refine ⟨?_, lookup_append_map_prefix pfx fun hnot => ?_⟩
    · by_cases hmem : x ∈ patBoundVars p
      · exact List.mem_append_left _ hmem
      · exact List.mem_append_right _ (hag x (by simp [hasFreeVarArms, hmem, hfb])).1
    · rw [hp.dom_eq] at hnot
      exact (hag x (by simp [hasFreeVarArms, hnot, hfb])).2

end

section PrefixEval

variable {F : Type} [Field F] [DecidableEq F]

private theorem find?_append_map_prefix {α : Type} (pfx : String)
    {bs loc1 loc2 : List (String × α)} {x : String}
    (hnot : x ∉ bs.map Prod.fst →
      (loc1.find? (·.1 == x)).map Prod.snd = (loc2.find? (·.1 == pfx ++ x)).map Prod.snd) :
    ((bs ++ loc1).find? (·.1 == x)).map Prod.snd =
      (((bs.map fun q => (pfx ++ q.1, q.2)) ++ loc2).find? (·.1 == pfx ++ x)).map Prod.snd := by
  induction bs with
  | nil => exact hnot (by simp)
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.cons_append, List.find?_cons]
    by_cases hx : k = x
    · subst hx; simp
    · have hne : pfx ++ k ≠ pfx ++ x := fun heq => hx (string_append_left_inj heq)
      simp only [beq_false_of_ne hx, beq_false_of_ne hne]
      exact ih fun hn => hnot (by simp [Ne.symm hx, hn])

omit [DecidableEq F] in
private theorem map_qualifyPatF_eq (ps : List Pat) :
    List.map (Aiur.Generic.Pattern.map (Nat.cast : Nat → F)) (List.map qualifyPat ps) =
      ps.map (qualifyPatF F) := by
  induction ps with
  | nil => rfl
  | cons p tl ih => simp [qualifyPatF, ih]

mutual

/-- Exact commutation of `World.matchPattern` with `prefixPat` on simple patterns. -/
theorem matchPattern_prefixPat {world : World F} {h : Heap F} (pfx : String) :
    ∀ {p : Pat} (v : SourceValue F), isSimplePat p = true →
      world.matchPattern [] h (qualifyPatF F (prefixPat pfx p)) v =
        (world.matchPattern [] h (qualifyPatF F p) v).map
          (Option.map (List.map fun q => (pfx ++ q.1, q.2)))
  | .wildcard, _, _ => by
    simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.map]
  | .literal n, v, _ => by
    cases v with
    | field x =>
      by_cases hx : (n : F) = x
      · subst hx
        simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.map]
      · simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
          matchPatternWith, Aiur.Pattern.bindings, hx, pure, Except.pure, Except.map]
    | _ =>
      simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, Except.map]
  | .bind x, _, _ => by
    simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
      matchPatternWith, pure, Except.pure, Except.map]
  | .tuple ps, v, hs => by
    cases v with
    | tuple vals =>
      simp only [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern]
      rw [matchPatternWith, matchPatternWith]
      simp only [List.length_map, prefixPatList_length]
      split
      · simp [pure, Except.pure, Except.map]
      · rw [matchListWith_attach, matchListWith_attach, map_qualifyPatF_eq, map_qualifyPatF_eq]
        exact matchListWith_prefixPatList pfx vals hs
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure, Except.map]
  | .array ps, v, hs => by
    cases v with
    | tuple vals =>
      simp only [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern]
      rw [matchPatternWith, matchPatternWith]
      simp only [List.length_map, prefixPatList_length]
      split
      · simp [pure, Except.pure, Except.map]
      · rw [matchListWith_attach, matchListWith_attach, map_qualifyPatF_eq, map_qualifyPatF_eq]
        exact matchListWith_prefixPatList pfx vals hs
    | field _ | ptr _ _ | construct _ _ _ =>
      simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure, Except.map]
  | .construct ty nm ps, v, hs => by
    cases v with
    | construct ty' nm' vals =>
      simp only [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern]
      rw [matchPatternWith, matchPatternWith]
      simp only [List.length_map, prefixPatList_length]
      split
      · simp [pure, Except.pure, Except.map]
      · rw [matchListWith_attach, matchListWith_attach, map_qualifyPatF_eq, map_qualifyPatF_eq]
        exact matchListWith_prefixPatList pfx vals hs
    | field _ | ptr _ _ | tuple _ =>
      simp [prefixPat, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern,
        matchPatternWith, pure, Except.pure, Except.map]
  | .global _ _, _, hs | .load _, _, hs | .orElse _ _ _, _, hs | .repeat _ _, _, hs
  | .record _ _, _, hs | .constructAs _ _ _ _, _, hs => by simp [isSimplePat] at hs
termination_by p _ _ => sizeOf p

theorem matchListWith_prefixPatList {world : World F} {h : Heap F} (pfx : String) :
    ∀ {ps : List Pat} (vals : List (SourceValue F)), isSimplePatList ps = true →
      matchListWith (fun p v => world.matchPattern [] h p v)
          ((prefixPatList pfx ps).map (qualifyPatF F)) vals =
        (matchListWith (fun p v => world.matchPattern [] h p v)
          (ps.map (qualifyPatF F)) vals).map
          (Option.map (List.map fun q => (pfx ++ q.1, q.2)))
  | [], [], _ => by simp [prefixPatList, matchListWith, pure, Except.pure, Except.map]
  | [], _ :: _, _ => by simp [prefixPatList, matchListWith, pure, Except.pure, Except.map]
  | _ :: _, [], _ => by simp [prefixPatList, matchListWith, pure, Except.pure, Except.map]
  | p :: ps, v :: vs, hs => by
    simp only [isSimplePatList, Bool.and_eq_true] at hs
    simp only [prefixPatList, List.map_cons, matchListWith]
    rw [matchPattern_prefixPat pfx v hs.1]
    cases hm : world.matchPattern [] h (qualifyPatF F p) v with
    | error err => simp [bind, Except.bind, Except.map]
    | ok opt =>
      cases opt with
      | none => simp [bind, Except.bind, pure, Except.pure, Except.map]
      | some bs1 =>
        simp only [bind, Except.bind, Except.map, Option.map_some]
        rw [matchListWith_prefixPatList pfx vs hs.2]
        cases htl : matchListWith (fun p v => world.matchPattern [] h p v) (ps.map (qualifyPatF F)) vs with
        | error err => simp [Except.map]
        | ok opt2 =>
          cases opt2 with
          | none => simp [pure, Except.pure, Except.map]
          | some bs2 => simp [pure, Except.pure, Except.map, List.map_append]
termination_by ps _ _ => sizeOf ps

end

theorem selectArm_prefixArms {world : World F} {h : Heap F} (pfx : String) (scope : List String) :
    ∀ {arms : List (Pat × Expr)} {v : SourceValue F} {bs' : Environment F Nat}
      {branch' : Aiur.Generic.Expr F},
      isCleanArms arms = true →
      SourceSemantics.selectArm world [] h v
          ((prefixArms pfx scope arms).map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
        .ok (some (bs', branch')) →
      ∃ p b bs, (p, b) ∈ arms ∧
        bs' = bs.map (fun q => (pfx ++ q.1, q.2)) ∧
        branch' = qualifyExprF F (prefixExpr pfx (patBoundVars p ++ scope) b) ∧
        world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) ∧
        SourceSemantics.selectArm world [] h v
          (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
          .ok (some (bs, qualifyExprF F b))
  | [], _, _, _, _, hsel => by simp [prefixArms, SourceSemantics.selectArm, pure, Except.pure] at hsel
  | (p, b) :: rest, v, bs', branch', hclean, hsel => by
    simp only [isCleanArms, Bool.and_eq_true] at hclean
    simp only [prefixArms, List.map_cons, SourceSemantics.selectArm] at hsel ⊢
    rw [matchPattern_prefixPat pfx v hclean.1.1] at hsel
    cases hm : world.matchPattern [] h (qualifyPatF F p) v with
    | error err => simp [hm, bind, Except.bind, Except.map] at hsel
    | ok opt =>
      cases opt with
      | none =>
        simp only [hm, Except.map, Option.map_none, bind, Except.bind] at hsel ⊢
        obtain ⟨p0, b0, bs0, hmem, hbs, hbr, hm0, hsel0⟩ :=
          selectArm_prefixArms pfx scope hclean.2 hsel
        exact ⟨p0, b0, bs0, List.mem_cons_of_mem _ hmem, hbs, hbr, hm0, hsel0⟩
      | some bs =>
        simp only [hm, Except.map, Option.map_some, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel ⊢
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨p, b, bs, List.mem_cons_self, rfl, rfl, hm, ⟨rfl, rfl⟩⟩

mutual

/-- **Alpha-Renaming Backward Soundness for `prefixExpr`:**
Any `EvalExpr` derivation on `prefixExpr pfx scope e` transfers back to `e`! -/
theorem evalExpr_prefixExpr_backward {world : World F} (pfx : String) :
    ∀ (scope : List String) {locOrig locPref : Environment F Nat} {e : Expr}
      {h h' : Heap F} {r : SourceValue F},
      isCleanExpr e = true →
      (∀ x, hasFreeVar x e = true →
        x ∈ scope ∧ (locOrig.find? (·.1 == x)).map Prod.snd = (locPref.find? (·.1 == pfx ++ x)).map Prod.snd) →
      EvalExpr world [] locPref (qualifyExprF F (prefixExpr pfx scope e)) h r h' →
      EvalExpr world [] locOrig (qualifyExprF F e) h r h'
  | _, _, _, .control .., _, _, _, hc, _, _ | _, _, _, .global .., _, _, _, hc, _, _ => by
    simp [isCleanExpr] at hc
  | _, _, _, .literal _, _, _, _, _, _, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev; exact .literal
  | scope, locOrig, locPref, .var x, _, _, r, _, hag, ev => by
    obtain ⟨hmem, heq⟩ := hag x (by simp [hasFreeVar])
    have hcont : scope.contains x = true := List.contains_iff_mem.mpr hmem
    simp only [prefixExpr, hcont, ↓reduceIte, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | var hl =>
      rw [hl] at heq
      cases ho : locOrig.find? (·.1 == x) with
      | none => rw [ho] at heq; cases heq
      | some kv =>
        rw [ho] at heq
        simp only [Option.map_some, Option.some.injEq] at heq
        rcases kv with ⟨k, v⟩; dsimp only at heq; subst heq
        have hk : k = x := by simpa [beq_iff_eq] using List.find?_some ho
        subst hk
        exact .var ho
  | scope, _, _, .tuple xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple evs =>
      exact .tuple (evalArgs_prefixExprList_backward pfx scope hc hag evs)
  | scope, _, _, .array xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array evs =>
      exact .array (evalArgs_prefixExprList_backward pfx scope hc hag evs)
  | scope, _, _, .construct _ _ _ xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct evs =>
      exact .construct (evalArgs_prefixExprList_backward pfx scope hc hag evs)
  | scope, _, _, .constructAs _ _ _ xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | constructAs evs =>
      exact .constructAs (evalArgs_prefixExprList_backward pfx scope hc hag evs)
  | scope, _, _, .record _ xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | record evs =>
      exact .record (evalArgs_prefixExprList_backward pfx scope hc hag evs)
  | scope, _, _, .update _ xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | update evs ha =>
      exact .update (evalArgs_prefixExprList_backward pfx scope hc hag evs) ha
  | scope, _, _, .builtin _ xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin evs ha =>
      exact .builtin (evalArgs_prefixExprList_backward pfx scope hc hag evs) ha
  | scope, _, _, .call _ _ xs, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | call evs hfn =>
      exact .call (evalArgs_prefixExprList_backward pfx scope hc hag evs) hfn
  | scope, _, _, .repeat x _, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item =>
      exact .repeat (evalExpr_prefixExpr_backward pfx scope hc hag item)
  | scope, _, _, .index x _, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp =>
      exact .index (evalExpr_prefixExpr_backward pfx scope hc hag item) hp
  | scope, _, _, .slice x _ _, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs =>
      exact .slice (evalExpr_prefixExpr_backward pfx scope hc hag item) hs
  | scope, _, _, .member x _, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | member item hp =>
      exact .member (evalExpr_prefixExpr_backward pfx scope hc hag item) hp
  | scope, _, _, .project x _, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp =>
      exact .project (evalExpr_prefixExpr_backward pfx scope hc hag item) hp
  | scope, _, _, .store x, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item =>
      exact .store (evalExpr_prefixExpr_backward pfx scope hc hag item)
  | scope, _, _, .load x, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl =>
      exact .load (evalExpr_prefixExpr_backward pfx scope hc hag item) hl
  | scope, _, _, .hint _ x _, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht =>
      exact .hint (evalExpr_prefixExpr_backward pfx scope (e := x) hc hag item) ht
  | scope, _, _, .neg x, _, _, _, hc, hag, ev => by
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop =>
      exact .neg (evalExpr_prefixExpr_backward pfx scope hc hag item) hop
  | scope, _, _, .binary _ l r, _, _, _, hc, hag, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | binary evL evR hop =>
      exact .binary
        (evalExpr_prefixExpr_backward pfx scope hc.1 (fun x hx => hag x (by simp [hasFreeVar, hx])) evL)
        (evalExpr_prefixExpr_backward pfx scope hc.2 (fun x hx => hag x (by simp [hasFreeVar, hx])) evR) hop
  | scope, locOrig, locPref, .letValue p x b, _, _, _, hc, hag, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [prefixExpr] at ev
    rw [qualifyExprF_letValue] at ev ⊢
    cases ev with | letValue evX hm' evB =>
      rename_i val middle bs'
      have evXOrig := evalExpr_prefixExpr_backward pfx scope hc.1.2
        (fun z hz => hag z (by simp [hasFreeVar, hz])) evX
      rw [matchPattern_prefixPat pfx val hc.1.1] at hm'
      cases hm : world.matchPattern [] middle (qualifyPatF F p) val with
      | error err => simp [hm, Except.map] at hm'
      | ok opt =>
        cases opt with
        | none => simp [hm, Except.map] at hm'
        | some bs =>
          simp only [hm, Except.map, Option.map_some, Except.ok.injEq,
            Option.some.injEq] at hm'
          subst hm'
          have hdom := matchPattern_names_of_simple hc.1.1 hm
          refine .letValue evXOrig hm (evalExpr_prefixExpr_backward pfx (patBoundVars p ++ scope) hc.2 ?_ evB)
          intro z hfz
          refine ⟨?_, find?_append_map_prefix pfx fun hnot => ?_⟩
          · by_cases hp : z ∈ patBoundVars p
            · exact List.mem_append_left _ hp
            · exact List.mem_append_right _ (hag z (by simp [hasFreeVar, hp, hfz])).1
          · rw [hdom] at hnot
            exact (hag z (by simp [hasFreeVar, hnot, hfz])).2
  | scope, locOrig, locPref, .matchValue s arms, _, _, _, hc, hag, ev => by
    simp only [isCleanExpr, Bool.and_eq_true] at hc
    simp only [prefixExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | matchValue evS hsel evB =>
      have evSOrig := evalExpr_prefixExpr_backward pfx scope hc.1
        (fun z hz => hag z (by simp [hasFreeVar, hz])) evS
      rw [map_qualifyArmsF] at hsel
      obtain ⟨p, b, bs, hmem, rfl, rfl, hm, hselOrig⟩ :=
        selectArm_prefixArms pfx scope hc.2 hsel
      obtain ⟨hpSimple, hbClean⟩ := isCleanArms_iff.mp hc.2 (p, b) hmem
      have hdom := matchPattern_names_of_simple hpSimple hm
      rw [← map_qualifyArmsF] at hselOrig
      refine .matchValue evSOrig hselOrig
        (evalExpr_prefixExpr_backward pfx (patBoundVars p ++ scope) hbClean ?_ evB)
      have harmFree : ∀ z, z ∉ patBoundVars p → hasFreeVar z b = true →
          hasFreeVarArms z arms = true := by
        clear hselOrig hsel evB evS evSOrig hm hdom hag hc
        intro z hnot hfz
        induction arms with
        | nil => cases hmem
        | cons hd tl ih =>
          rcases hd with ⟨p0, b0⟩
          simp only [hasFreeVarArms, Bool.or_eq_true]
          rcases List.mem_cons.mp hmem with heq | htl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            exact Or.inl (by simp [hnot, hfz])
          · exact Or.inr (ih htl)
      intro z hfz
      refine ⟨?_, find?_append_map_prefix pfx fun hnot => ?_⟩
      · by_cases hp : z ∈ patBoundVars p
        · exact List.mem_append_left _ hp
        · exact List.mem_append_right _ (hag z (by simp [hasFreeVar, harmFree z hp hfz])).1
      · rw [hdom] at hnot
        exact (hag z (by simp [hasFreeVar, harmFree z hnot hfz])).2
termination_by _ _ _ e _ _ _ _ _ _ => sizeOf e
decreasing_by
  all_goals try simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_prefixExprList_backward {world : World F} (pfx : String) :
    ∀ (scope : List String) {locOrig locPref : Environment F Nat} {xs : List Expr}
      {h h' : Heap F} {vs : List (SourceValue F)},
      isCleanList xs = true →
      (∀ x, hasFreeVarList x xs = true →
        x ∈ scope ∧ (locOrig.find? (·.1 == x)).map Prod.snd = (locPref.find? (·.1 == pfx ++ x)).map Prod.snd) →
      EvalArgs world [] locPref ((prefixExprList pfx scope xs).map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locOrig (xs.map (qualifyExprF F)) h vs h'
  | _, _, _, [], _, _, _, _, _, ev => by cases ev; exact .nil
  | scope, _, _, x :: xs, _, _, _, hc, hag, ev => by
    simp only [isCleanList, Bool.and_eq_true] at hc
    cases ev with | cons evH evT =>
      exact .cons
        (evalExpr_prefixExpr_backward pfx scope hc.1 (fun z hz => hag z (by simp [hasFreeVarList, hz])) evH)
        (evalArgs_prefixExprList_backward pfx scope hc.2 (fun z hz => hag z (by simp [hasFreeVarList, hz])) evT)
termination_by _ _ _ xs _ _ _ _ _ _ => sizeOf xs

end

end PrefixEval

/-! ### Part 7D: `bindParams` Properties & Evaluation Inversion -/

theorem hasFreeVar_bindParams (pfx : String) :
    ∀ (pNames : List String) (xs : List Expr) (body : Expr) (v : String),
      pNames.length = xs.length →
      hasFreeVar v (bindParams pfx (pNames.zip xs) body) = true →
      hasFreeVarList v xs = true ∨ (v ∉ pNames.map (pfx ++ ·) ∧ hasFreeVar v body = true)
  | [], [], body, v, _, h => Or.inr ⟨by simp, h⟩
  | p :: ps, x :: xs, body, v, hlen, h => by
    simp only [List.zip_cons_cons, bindParams, hasFreeVar, patBoundVars, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with hx | ⟨hne, hrest⟩
    · exact Or.inl (by simp [hasFreeVarList, hx])
    · have hvne : v ≠ pfx ++ p := by intro heq; subst heq; simp at hne
      rcases hasFreeVar_bindParams pfx ps xs body v (Nat.succ.inj hlen) hrest with hxs | ⟨hnot, hb⟩
      · exact Or.inl (by simp [hasFreeVarList, hxs])
      · exact Or.inr ⟨by simp [hvne, hnot], hb⟩

theorem hasBoundVar_bindParams (pfx : String) :
    ∀ (pNames : List String) (xs : List Expr) (body : Expr) (v : String),
      pNames.length = xs.length →
      hasBoundVar v (bindParams pfx (pNames.zip xs) body) = true →
      v ∈ pNames.map (pfx ++ ·) ∨ hasBoundVarList v xs = true ∨ hasBoundVar v body = true
  | [], [], _, _, _, h => Or.inr (Or.inr h)
  | p :: ps, x :: xs, body, v, hlen, h => by
    simp only [List.zip_cons_cons, bindParams, hasBoundVar, patBoundVars, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | hx) | hrest
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp [hasBoundVarList, hx]))
    · rcases hasBoundVar_bindParams pfx ps xs body v (Nat.succ.inj hlen) hrest with hp | hxs | hb
      · exact Or.inl (by simp [hp])
      · exact Or.inr (Or.inl (by simp [hasBoundVarList, hxs]))
      · exact Or.inr (Or.inr hb)

theorem literalsBounded_bindParams (pfx : String) :
    ∀ (pNames : List String) (xs : List Expr) (body : Expr),
      pNames.length = xs.length →
      literalsBoundedList xs = true → literalsBounded body = true →
      literalsBounded (bindParams pfx (pNames.zip xs) body) = true
  | [], [], _, _, _, hb => hb
  | _ :: ps, _ :: xs, body, hlen, hxs, hb => by
    simp only [literalsBoundedList, Bool.and_eq_true] at hxs
    simp only [List.zip_cons_cons, bindParams, literalsBounded, Bool.and_eq_true]
    exact ⟨hxs.1, literalsBounded_bindParams pfx ps xs body (Nat.succ.inj hlen) hxs.2 hb⟩

theorem noInlinableInBoundedCalls_bindParams (pfx : String) :
    ∀ (pNames : List String) (xs : List Expr) (body : Expr),
      pNames.length = xs.length →
      noInlinableInBoundedCallsList xs = true → noInlinableInBoundedCalls body = true →
      noInlinableInBoundedCalls (bindParams pfx (pNames.zip xs) body) = true
  | [], [], _, _, _, hb => hb
  | _ :: ps, _ :: xs, body, hlen, hxs, hb => by
    simp only [noInlinableInBoundedCallsList, Bool.and_eq_true] at hxs
    simp only [List.zip_cons_cons, bindParams, noInlinableInBoundedCalls, Bool.and_eq_true]
    exact ⟨hxs.1, noInlinableInBoundedCalls_bindParams pfx ps xs body (Nat.succ.inj hlen) hxs.2 hb⟩

theorem noLetShadow_bindParams (pfx : String) :
    ∀ (pNames : List String) (xs : List Expr) (body : Expr) (scope : List String),
      pNames.length = xs.length →
      pNames.Nodup →
      NoLetShadowList scope xs →
      (∀ s ∈ scope, ∀ p ∈ pNames, s ≠ pfx ++ p) →
      (∀ v, hasBoundVarList v xs = true → (∀ p ∈ pNames, v ≠ pfx ++ p) ∧ hasBoundVar v body = false) →
      NoLetShadow (pNames.map (pfx ++ ·) ++ scope) body →
      NoLetShadow scope (bindParams pfx (pNames.zip xs) body)
  | [], [], body, scope, _, _, _, _, _, hb => hb
  | p :: ps, x :: xs, body, scope, hlen, hnd, ⟨hdisjX, hnsX, hnsXs⟩, hsc, hbv, hb => by
    simp only [List.nodup_cons] at hnd
    simp only [List.zip_cons_cons, bindParams, NoLetShadow, patBoundVars]
    refine ⟨fun v hv hmem => ?_, fun v hv => ?_, hnsX, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv
      exact hsc _ hmem p List.mem_cons_self rfl
    · obtain ⟨hnp, hnb⟩ := hbv v (by simp [hasBoundVarList, hv])
      refine ⟨fun hm => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; exact hnp p List.mem_cons_self hm
      · cases hrb : hasBoundVar v (bindParams pfx (ps.zip xs) body) with
        | false => rfl
        | true =>
          rcases hasBoundVar_bindParams pfx ps xs body v (Nat.succ.inj hlen) hrb with h1 | h2 | h3
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
            exact absurd rfl (hnp q (List.mem_cons_of_mem _ hq))
          · rw [hdisjX v hv] at h2; cases h2
          · rw [hnb] at h3; cases h3
    · refine noLetShadow_bindParams pfx ps xs body ((pfx ++ p) :: scope) (Nat.succ.inj hlen) hnd.2
        (noLetShadowList_scope_imp (fun v hv => ?_) hnsXs) ?_ ?_ ?_
      · rcases List.mem_cons.mp hv with rfl | htl
        · refine Or.inr ?_
          cases hxb : hasBoundVarList (pfx ++ p) xs with
          | false => rfl
          | true => exact absurd rfl ((hbv _ (by simp [hasBoundVarList, hxb])).1 p List.mem_cons_self)
        · exact Or.inl htl
      · intro s hs q hq
        rcases List.mem_cons.mp hs with rfl | htl
        · intro heq; exact hnd.1 (string_append_left_inj heq ▸ hq)
        · exact hsc s htl q (List.mem_cons_of_mem _ hq)
      · intro v hv
        obtain ⟨h1, h2⟩ := hbv v (by simp [hasBoundVarList, hv])
        exact ⟨fun q hq => h1 q (List.mem_cons_of_mem _ hq), h2⟩
      · refine noLetShadow_scope_imp (fun v hv => Or.inl ?_) hb
        rcases List.mem_append.mp hv with h1 | h2
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ h1)
        · rcases List.mem_cons.mp h2 with rfl | htl
          · exact List.mem_append_left _ List.mem_cons_self
          · exact List.mem_append_right _ htl

theorem hasTy_bindParams {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} (pfx : String) :
    ∀ (params : List (String × Lower.Ty)) (xs : List Expr) (Γ : TyEnv) (body : Expr) (rty : Lower.Ty),
      HasTyList sigs enums Γ xs (params.map Prod.snd) →
      (∀ p ∈ params.map Prod.fst, hasFreeVarList (pfx ++ p) xs = false) →
      HasTy sigs enums ((params.map fun q => (pfx ++ q.1, q.2)).reverse ++ Γ) body rty →
      HasTy sigs enums Γ (bindParams pfx ((params.map Prod.fst).zip xs) body) rty
  | [], [], _, _, _, .nil, _, hb => hb
  | (p, tp) :: rest, x :: xs, Γ, body, rty, .cons hx hxs, hnf, hb => by
    simp only [List.map_cons, List.zip_cons_cons, bindParams]
    refine .letValue hx .bind ?_
    have hnfP : hasFreeVarList (pfx ++ p) xs = false := by
      have h0 := hnf p (by simp)
      simp only [hasFreeVarList, Bool.or_eq_false_iff] at h0; exact h0.2
    have hxs' : HasTyList sigs enums ((pfx ++ p, tp) :: Γ) xs (rest.map Prod.snd) := by
      refine hasTyList_envAgree hxs fun z hz => ?_
      have hne : z ≠ pfx ++ p := by intro heq; subst heq; rw [hnfP] at hz; cases hz
      simp [List.lookup, beq_false_of_ne hne]
    refine hasTy_bindParams pfx rest xs ((pfx ++ p, tp) :: Γ) body rty hxs' ?_ ?_
    · intro q hq
      have h0 := hnf q (by simp [hq])
      simp only [hasFreeVarList, Bool.or_eq_false_iff] at h0; exact h0.2
    · simpa [List.reverse_cons, List.append_assoc] using hb

section BindParamsEval

variable {F : Type} [Field F] [DecidableEq F]

/-- Invert `EvalExpr` on `bindParams pfx (pNames.zip xs) body` into `EvalArgs` on `xs` and
`EvalExpr` on `body` under the reversed parameter bindings! -/
theorem evalExpr_bindParams_inv {world : World F} (pfx : String) :
    ∀ (pNames : List String) (xs : List Expr) (body : Expr)
      {locals : Environment F Nat} {h h' : Heap F} {r : SourceValue F},
      pNames.length = xs.length →
      isCleanList xs = true →
      (∀ p ∈ pNames, hasFreeVarList (pfx ++ p) xs = false) →
      EvalExpr world [] locals (qualifyExprF F (bindParams pfx (pNames.zip xs) body)) h r h' →
      ∃ vs hm, vs.length = xs.length ∧
        EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs hm ∧
        EvalExpr world [] (((pNames.map (pfx ++ ·)).zip vs).reverse ++ locals)
          (qualifyExprF F body) hm r h'
  | [], [], body, locals, h, _, r, _, _, _, ev =>
    ⟨[], h, rfl, .nil, ev⟩
  | p :: ps, x :: xs, body, locals, h, h', r, hlen, hclean, hnf, ev => by
    simp only [isCleanList, Bool.and_eq_true] at hclean
    simp only [List.zip_cons_cons, bindParams] at ev
    obtain ⟨vx, h1, evX, evRest⟩ := evalExpr_let_bind_qual_inv ev
    have hnfP : hasFreeVarList (pfx ++ p) xs = false := by
      have h0 := hnf p List.mem_cons_self
      simp only [hasFreeVarList, Bool.or_eq_false_iff] at h0; exact h0.2
    obtain ⟨vs, hm, hlenVs, evXs', evBody⟩ := evalExpr_bindParams_inv pfx ps xs body
      (Nat.succ.inj hlen) hclean.2 (fun q hq => by
        have h0 := hnf q (List.mem_cons_of_mem _ hq)
        simp only [hasFreeVarList, Bool.or_eq_false_iff] at h0; exact h0.2) evRest
    have evXs : EvalArgs world [] locals (xs.map (qualifyExprF F)) h1 vs hm := by
      refine evalArgs_localsAgree hclean.2 (fun z hz => ?_) evXs'
      have hne : z ≠ pfx ++ p := by intro heq; subst heq; rw [hnfP] at hz; cases hz
      simp [beq_false_of_ne (Ne.symm hne)]
    refine ⟨vx :: vs, hm, congrArg Nat.succ hlenVs, .cons evX evXs, ?_⟩
    simpa [List.map_cons, List.zip_cons_cons, List.reverse_cons, List.append_assoc] using evBody

end BindParamsEval

/-! ### Part 7E: `InlineMapValid` & `inlineCallsM` Preservation + Backward Soundness -/

/-- Counter-independent validity invariant on the inlining table `imap`: every mapped callee
is well-typed, has distinct parameter names, satisfies `NoLetShadow`, `literalsBounded`,
`noInlinableInBoundedCalls`, and is provided by `world`. -/
structure InlineMapValid {F : Type} [Field F] [DecidableEq F]
    (world : World F) (sigs : FnSigs) (enums : List Aiur.Generic.EnumDecl)
    (imap : List (String × Fn)) : Prop where
  mem : ∀ nm callee, imap.lookup nm = some callee →
    callee.name = nm ∧
    callee.typeParams = [] ∧
    (nm.startsWith "f" || nm.startsWith "jp") = true ∧
    Lower.hasDoubleColon nm.toList = false ∧
    Lower.allDistinct (callee.params.map Prod.fst) = true ∧
    sigs (qualified nm) = some (callee.params.map Prod.snd, callee.result) ∧
    WorldProvidesFn world (qualified nm) (callee.params.map Prod.fst) (qualifyExprF F callee.body) ∧
    HasTy sigs enums callee.params callee.body callee.result ∧
    NoLetShadow (callee.params.map Prod.fst) callee.body ∧
    literalsBounded callee.body = true ∧
    noInlinableInBoundedCalls callee.body = true

/-- Helper to unpack `(m >>= f).run s` cleanly without leaving `match` expressions. -/
private theorem stateM_bind_eq {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := by
  change (match m.run s with | (a, s') => (f a).run s') = _
  cases m.run s; rfl

private theorem inlineCallsM_run_tuple (imap : List (String × Fn)) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.tuple xs)).run c =
      (.tuple ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_array (imap : List (String × Fn)) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.array xs)).run c =
      (.array ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_construct (imap : List (String × Fn)) (ty : String)
    (targs : Option (List Lower.Ty)) (nm : String) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.construct ty targs nm xs)).run c =
      (.construct ty targs nm ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_constructAs (imap : List (String × Fn)) (ps : List String)
    (ty : Lower.Ty) (nm : String) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.constructAs ps ty nm xs)).run c =
      (.constructAs ps ty nm ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_record (imap : List (String × Fn)) (hd : RecordHead) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.record hd xs)).run c =
      (.record hd ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_update (imap : List (String × Fn)) (ps : List UpdatePath)
    (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.update ps xs)).run c =
      (.update ps ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_builtin (imap : List (String × Fn)) (op : Builtin)
    (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.builtin op xs)).run c =
      (.builtin op ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_repeat (imap : List (String × Fn)) (x : Expr) (n c : Nat) :
    (inlineCallsM imap (.repeat x n)).run c =
      (.repeat ((inlineCallsM imap x).run c).1 n, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_index (imap : List (String × Fn)) (x : Expr) (i c : Nat) :
    (inlineCallsM imap (.index x i)).run c =
      (.index ((inlineCallsM imap x).run c).1 i, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_slice (imap : List (String × Fn)) (x : Expr) (a : Nat) (b : Option Nat) (c : Nat) :
    (inlineCallsM imap (.slice x a b)).run c =
      (.slice ((inlineCallsM imap x).run c).1 a b, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_member (imap : List (String × Fn)) (x : Expr) (f : FieldRef) (c : Nat) :
    (inlineCallsM imap (.member x f)).run c =
      (.member ((inlineCallsM imap x).run c).1 f, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_project (imap : List (String × Fn)) (x : Expr) (i c : Nat) :
    (inlineCallsM imap (.project x i)).run c =
      (.project ((inlineCallsM imap x).run c).1 i, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_store (imap : List (String × Fn)) (x : Expr) (c : Nat) :
    (inlineCallsM imap (.store x)).run c =
      (.store ((inlineCallsM imap x).run c).1, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_load (imap : List (String × Fn)) (x : Expr) (c : Nat) :
    (inlineCallsM imap (.load x)).run c =
      (.load ((inlineCallsM imap x).run c).1, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_hint (imap : List (String × Fn)) (ty : Lower.Ty) (x : Expr)
    (ch : String) (c : Nat) :
    (inlineCallsM imap (.hint ty x ch)).run c =
      (.hint ty ((inlineCallsM imap x).run c).1 ch, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_neg (imap : List (String × Fn)) (x : Expr) (c : Nat) :
    (inlineCallsM imap (.neg x)).run c =
      (.neg ((inlineCallsM imap x).run c).1, ((inlineCallsM imap x).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_binary (imap : List (String × Fn)) (op : BinOp)
    (l r : Expr) (c : Nat) :
    (inlineCallsM imap (.binary op l r)).run c =
      (.binary op ((inlineCallsM imap l).run c).1 ((inlineCallsM imap r).run ((inlineCallsM imap l).run c).2).1,
       ((inlineCallsM imap r).run ((inlineCallsM imap l).run c).2).2) := by
  rw [inlineCallsM, stateM_bind_eq, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_letValue (imap : List (String × Fn)) (p : Pat)
    (v b : Expr) (c : Nat) :
    (inlineCallsM imap (.letValue p v b)).run c =
      (.letValue p ((inlineCallsM imap v).run c).1 ((inlineCallsM imap b).run ((inlineCallsM imap v).run c).2).1,
       ((inlineCallsM imap b).run ((inlineCallsM imap v).run c).2).2) := by
  rw [inlineCallsM, stateM_bind_eq, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_matchValue (imap : List (String × Fn)) (s : Expr)
    (arms : List (Pat × Expr)) (c : Nat) :
    (inlineCallsM imap (.matchValue s arms)).run c =
      (.matchValue ((inlineCallsM imap s).run c).1 ((inlineCallsArmsM imap arms).run ((inlineCallsM imap s).run c).2).1,
       ((inlineCallsArmsM imap arms).run ((inlineCallsM imap s).run c).2).2) := by
  rw [inlineCallsM, stateM_bind_eq, stateM_bind_eq]; rfl

private theorem inlineCallsListM_run_nil (imap : List (String × Fn)) (c : Nat) :
    (inlineCallsListM imap []).run c = ([], c) := rfl

private theorem inlineCallsListM_run_cons (imap : List (String × Fn)) (x : Expr)
    (xs : List Expr) (c : Nat) :
    (inlineCallsListM imap (x :: xs)).run c =
      (((inlineCallsM imap x).run c).1 :: ((inlineCallsListM imap xs).run ((inlineCallsM imap x).run c).2).1,
       ((inlineCallsListM imap xs).run ((inlineCallsM imap x).run c).2).2) := by
  rw [inlineCallsListM, stateM_bind_eq, stateM_bind_eq]; rfl

private theorem inlineCallsArmsM_run_cons (imap : List (String × Fn)) (p : Pat) (b : Expr)
    (rest : List (Pat × Expr)) (c : Nat) :
    (inlineCallsArmsM imap ((p, b) :: rest)).run c =
      ((p, ((inlineCallsM imap b).run c).1) :: ((inlineCallsArmsM imap rest).run ((inlineCallsM imap b).run c).2).1,
       ((inlineCallsArmsM imap rest).run ((inlineCallsM imap b).run c).2).2) := by
  rw [inlineCallsArmsM, stateM_bind_eq, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_call_none (imap : List (String × Fn)) (nm : String)
    (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.call nm none xs)).run c =
      (.call nm none ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_call_cons (imap : List (String × Fn)) (nm : String)
    (t0 : Lower.Ty) (ts : List Lower.Ty) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.call nm (some (t0 :: ts)) xs)).run c =
      (.call nm (some (t0 :: ts)) ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq]; rfl

private theorem inlineCallsM_run_call_lookup_none (imap : List (String × Fn)) (nm : String)
    (xs : List Expr) (c : Nat) (hl : imap.lookup nm = none) :
    (inlineCallsM imap (.call nm (some []) xs)).run c =
      (.call nm (some []) ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq, hl]; rfl

private theorem inlineCallsM_run_call_inline (imap : List (String × Fn)) (nm : String)
    (xs : List Expr) (c : Nat) (callee : Fn) (hl : imap.lookup nm = some callee)
    (hlen : callee.params.length = ((inlineCallsListM imap xs).run c).1.length) :
    (inlineCallsM imap (.call nm (some []) xs)).run c =
      (bindParams (inlinePfx ((inlineCallsListM imap xs).run c).2)
        ((callee.params.map Prod.fst).zip ((inlineCallsListM imap xs).run c).1)
        (prefixExpr (inlinePfx ((inlineCallsListM imap xs).run c).2)
          (callee.params.map Prod.fst) callee.body),
       ((inlineCallsListM imap xs).run c).2 + 1) := by
  rw [inlineCallsM, stateM_bind_eq, hl]
  dsimp only
  simp only [beq_iff_eq.mpr hlen, ↓reduceIte]
  rfl

private theorem inlineCallsM_run_call_len_ne (imap : List (String × Fn)) (nm : String)
    (xs : List Expr) (c : Nat) (callee : Fn) (hl : imap.lookup nm = some callee)
    (hlen : callee.params.length ≠ ((inlineCallsListM imap xs).run c).1.length) :
    (inlineCallsM imap (.call nm (some []) xs)).run c =
      (.call nm (some []) ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) := by
  rw [inlineCallsM, stateM_bind_eq, hl]
  dsimp only
  rw [beq_false_of_ne hlen]
  rfl

private theorem inlineCallsM_run_call_cases (imap : List (String × Fn)) (nm : String)
    (targs : Option (List Lower.Ty)) (xs : List Expr) (c : Nat) :
    (inlineCallsM imap (.call nm targs xs)).run c =
      (.call nm targs ((inlineCallsListM imap xs).run c).1, ((inlineCallsListM imap xs).run c).2) ∨
    (∃ callee, targs = some [] ∧ imap.lookup nm = some callee ∧
      callee.params.length = ((inlineCallsListM imap xs).run c).1.length ∧
      (inlineCallsM imap (.call nm targs xs)).run c =
        (bindParams (inlinePfx ((inlineCallsListM imap xs).run c).2)
          ((callee.params.map Prod.fst).zip ((inlineCallsListM imap xs).run c).1)
          (prefixExpr (inlinePfx ((inlineCallsListM imap xs).run c).2)
            (callee.params.map Prod.fst) callee.body),
         ((inlineCallsListM imap xs).run c).2 + 1)) := by
  cases targs with
  | none => exact Or.inl (inlineCallsM_run_call_none imap nm xs c)
  | some ts =>
    cases ts with
    | cons t0 ts' => exact Or.inl (inlineCallsM_run_call_cons imap nm t0 ts' xs c)
    | nil =>
      cases hl : imap.lookup nm with
      | none => exact Or.inl (inlineCallsM_run_call_lookup_none imap nm xs c hl)
      | some callee =>
        by_cases hlen : callee.params.length = ((inlineCallsListM imap xs).run c).1.length
        · exact Or.inr ⟨callee, rfl, rfl, hlen, inlineCallsM_run_call_inline imap nm xs c callee hl hlen⟩
        · exact Or.inl (inlineCallsM_run_call_len_ne imap nm xs c callee hl hlen)

mutual

theorem inlineCallsM_of_noInlinableCalls {imap : List (String × Fn)}
    (hnames : ∀ nm callee, imap.lookup nm = some callee → (nm.startsWith "f" || nm.startsWith "jp") = true) :
    ∀ {e : Expr} (c : Nat), noInlinableCalls e = true → (inlineCallsM imap e).run c = (e, c)
  | .literal _, _, _ | .var _, _, _ | .global _ _, _, _ | .control _ _, _, _ => rfl
  | .tuple xs, c, h => by rw [inlineCallsM_run_tuple, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .array xs, c, h => by rw [inlineCallsM_run_array, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .construct _ _ _ xs, c, h => by rw [inlineCallsM_run_construct, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .constructAs _ _ _ xs, c, h => by rw [inlineCallsM_run_constructAs, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .record _ xs, c, h => by rw [inlineCallsM_run_record, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .update _ xs, c, h => by rw [inlineCallsM_run_update, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .builtin _ xs, c, h => by rw [inlineCallsM_run_builtin, inlineCallsListM_of_noInlinableCalls hnames c h]
  | .repeat x _, c, h => by rw [inlineCallsM_run_repeat, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .index x _, c, h => by rw [inlineCallsM_run_index, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .slice x _ _, c, h => by rw [inlineCallsM_run_slice, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .member x _, c, h => by rw [inlineCallsM_run_member, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .project x _, c, h => by rw [inlineCallsM_run_project, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .store x, c, h => by rw [inlineCallsM_run_store, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .load x, c, h => by rw [inlineCallsM_run_load, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .hint _ x _, c, h => by rw [inlineCallsM_run_hint, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .neg x, c, h => by rw [inlineCallsM_run_neg, inlineCallsM_of_noInlinableCalls hnames c (e := x) h]
  | .binary _ l r, c, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    rw [inlineCallsM_run_binary, inlineCallsM_of_noInlinableCalls hnames c h.1,
        inlineCallsM_of_noInlinableCalls hnames c h.2]
  | .letValue _ v b, c, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    rw [inlineCallsM_run_letValue, inlineCallsM_of_noInlinableCalls hnames c h.1,
        inlineCallsM_of_noInlinableCalls hnames c h.2]
  | .matchValue s arms, c, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    rw [inlineCallsM_run_matchValue, inlineCallsM_of_noInlinableCalls hnames c h.1,
        inlineCallsArmsM_of_noInlinableCalls hnames c h.2]
  | .call nm targs xs, c, h => by
    simp only [noInlinableCalls, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hnone : imap.lookup nm = none := by
      cases hl : imap.lookup nm with
      | none => rfl
      | some callee =>
        have htr := hnames nm callee hl
        rw [htr] at h; cases h.1
    have hxs := inlineCallsListM_of_noInlinableCalls hnames c h.2
    cases targs with
    | none => rw [inlineCallsM_run_call_none, hxs]
    | some ts =>
      cases ts with
      | cons _ _ => rw [inlineCallsM_run_call_cons, hxs]
      | nil => rw [inlineCallsM_run_call_lookup_none imap nm xs c hnone, hxs]
termination_by e _ _ => sizeOf e

theorem inlineCallsListM_of_noInlinableCalls {imap : List (String × Fn)}
    (hnames : ∀ nm callee, imap.lookup nm = some callee → (nm.startsWith "f" || nm.startsWith "jp") = true) :
    ∀ {xs : List Expr} (c : Nat), noInlinableCallsList xs = true →
      (inlineCallsListM imap xs).run c = (xs, c)
  | [], _, _ => rfl
  | x :: xs, c, h => by
    simp only [noInlinableCallsList, Bool.and_eq_true] at h
    rw [inlineCallsListM_run_cons, inlineCallsM_of_noInlinableCalls hnames c h.1,
        inlineCallsListM_of_noInlinableCalls hnames c h.2]
termination_by xs _ _ => sizeOf xs

theorem inlineCallsArmsM_of_noInlinableCalls {imap : List (String × Fn)}
    (hnames : ∀ nm callee, imap.lookup nm = some callee → (nm.startsWith "f" || nm.startsWith "jp") = true) :
    ∀ {arms : List (Pat × Expr)} (c : Nat), noInlinableCallsArms arms = true →
      (inlineCallsArmsM imap arms).run c = (arms, c)
  | [], _, _ => rfl
  | (p, b) :: rest, c, h => by
    simp only [noInlinableCallsArms, Bool.and_eq_true] at h
    rw [inlineCallsArmsM_run_cons, inlineCallsM_of_noInlinableCalls hnames c h.1,
        inlineCallsArmsM_of_noInlinableCalls hnames c h.2]
termination_by arms _ _ => sizeOf arms

end

theorem inlineCallsListM_length (imap : List (String × Fn)) :
    ∀ (xs : List Expr) (c : Nat), ((inlineCallsListM imap xs).run c).1.length = xs.length
  | [], _ => rfl
  | x :: xs, c => by
    rw [inlineCallsListM_run_cons]
    exact congrArg Nat.succ (inlineCallsListM_length imap xs _)

mutual

/-- Counter monotonicity, free-variable preservation, and bound-variable freshness for `inlineCallsM`! -/
theorem inlineCallsM_vars {imap : List (String × Fn)}
    (hclosed : ∀ nm callee, imap.lookup nm = some callee →
      ∀ u, hasFreeVar u callee.body = true → u ∈ callee.params.map Prod.fst) :
    ∀ (e : Expr) (c : Nat),
      c ≤ ((inlineCallsM imap e).run c).2 ∧
      (∀ v, hasFreeVar v ((inlineCallsM imap e).run c).1 = true → hasFreeVar v e = true) ∧
      (∀ v, hasBoundVar v ((inlineCallsM imap e).run c).1 = true →
        hasBoundVar v e = true ∨
        ∃ k u, c ≤ k ∧ k < ((inlineCallsM imap e).run c).2 ∧ v = inlinePfx k ++ u)
  | .literal _, c | .var _, c | .global _ _, c | .control _ _, c =>
    ⟨Nat.le_refl c, fun _ h => h, fun _ h => Or.inl h⟩
  | .tuple xs, c => by rw [inlineCallsM_run_tuple]; exact inlineCallsListM_vars hclosed xs c
  | .array xs, c => by rw [inlineCallsM_run_array]; exact inlineCallsListM_vars hclosed xs c
  | .construct _ _ _ xs, c => by rw [inlineCallsM_run_construct]; exact inlineCallsListM_vars hclosed xs c
  | .constructAs _ _ _ xs, c => by rw [inlineCallsM_run_constructAs]; exact inlineCallsListM_vars hclosed xs c
  | .record _ xs, c => by rw [inlineCallsM_run_record]; exact inlineCallsListM_vars hclosed xs c
  | .update _ xs, c => by rw [inlineCallsM_run_update]; exact inlineCallsListM_vars hclosed xs c
  | .builtin _ xs, c => by rw [inlineCallsM_run_builtin]; exact inlineCallsListM_vars hclosed xs c
  | .repeat x _, c => by rw [inlineCallsM_run_repeat]; exact inlineCallsM_vars hclosed x c
  | .index x _, c => by rw [inlineCallsM_run_index]; exact inlineCallsM_vars hclosed x c
  | .slice x _ _, c => by rw [inlineCallsM_run_slice]; exact inlineCallsM_vars hclosed x c
  | .member x _, c => by rw [inlineCallsM_run_member]; exact inlineCallsM_vars hclosed x c
  | .project x _, c => by rw [inlineCallsM_run_project]; exact inlineCallsM_vars hclosed x c
  | .store x, c => by rw [inlineCallsM_run_store]; exact inlineCallsM_vars hclosed x c
  | .load x, c => by rw [inlineCallsM_run_load]; exact inlineCallsM_vars hclosed x c
  | .hint _ x _, c => by rw [inlineCallsM_run_hint]; exact inlineCallsM_vars hclosed x c
  | .neg x, c => by rw [inlineCallsM_run_neg]; exact inlineCallsM_vars hclosed x c
  | .binary _ l r, c => by
    have hl := inlineCallsM_vars hclosed l c
    have hr := inlineCallsM_vars hclosed r ((inlineCallsM imap l).run c).2
    rw [inlineCallsM_run_binary]
    refine ⟨Nat.le_trans hl.1 hr.1, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [hasFreeVar, Bool.or_eq_true] at hv ⊢
      rcases hv with h1 | h2
      · exact Or.inl (hl.2.1 v h1)
      · exact Or.inr (hr.2.1 v h2)
    · simp only [hasBoundVar, Bool.or_eq_true] at hv ⊢
      rcases hv with h1 | h2
      · rcases hl.2.2 v h1 with h1' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inl h1')
        · exact Or.inr ⟨k, u, hk1, lt_of_lt_of_le hk2 hr.1, rfl⟩
      · rcases hr.2.2 v h2 with h2' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inr h2')
        · exact Or.inr ⟨k, u, Nat.le_trans hl.1 hk1, hk2, rfl⟩
  | .letValue p x b, c => by
    have hx := inlineCallsM_vars hclosed x c
    have hb := inlineCallsM_vars hclosed b ((inlineCallsM imap x).run c).2
    rw [inlineCallsM_run_letValue]
    refine ⟨Nat.le_trans hx.1 hb.1, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [hasFreeVar, Bool.or_eq_true, Bool.and_eq_true] at hv ⊢
      rcases hv with h1 | ⟨hnot, h2⟩
      · exact Or.inl (hx.2.1 v h1)
      · exact Or.inr ⟨hnot, hb.2.1 v h2⟩
    · simp only [hasBoundVar, Bool.or_eq_true] at hv ⊢
      rcases hv with (h0 | h1) | h2
      · exact Or.inl (Or.inl (Or.inl h0))
      · rcases hx.2.2 v h1 with h1' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inl (Or.inr h1'))
        · exact Or.inr ⟨k, u, hk1, lt_of_lt_of_le hk2 hb.1, rfl⟩
      · rcases hb.2.2 v h2 with h2' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inr h2')
        · exact Or.inr ⟨k, u, Nat.le_trans hx.1 hk1, hk2, rfl⟩
  | .matchValue s arms, c => by
    have hs := inlineCallsM_vars hclosed s c
    have ha := inlineCallsArmsM_vars hclosed arms ((inlineCallsM imap s).run c).2
    rw [inlineCallsM_run_matchValue]
    refine ⟨Nat.le_trans hs.1 ha.1, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [hasFreeVar, Bool.or_eq_true] at hv ⊢
      rcases hv with h1 | h2
      · exact Or.inl (hs.2.1 v h1)
      · exact Or.inr (ha.2.1 v h2)
    · simp only [hasBoundVar, Bool.or_eq_true] at hv ⊢
      rcases hv with h1 | h2
      · rcases hs.2.2 v h1 with h1' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inl h1')
        · exact Or.inr ⟨k, u, hk1, lt_of_lt_of_le hk2 ha.1, rfl⟩
      · rcases ha.2.2 v h2 with h2' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inr h2')
        · exact Or.inr ⟨k, u, Nat.le_trans hs.1 hk1, hk2, rfl⟩
  | .call nm targs xs, c => by
    have hxs := inlineCallsListM_vars hclosed xs c
    rcases inlineCallsM_run_call_cases imap nm targs xs c with hno | ⟨callee, _, hl, hlen, hres⟩
    · rw [hno]; exact hxs
    · rw [hres]
      let c1 := ((inlineCallsListM imap xs).run c).2
      let xs' := ((inlineCallsListM imap xs).run c).1
      have hlen' : (callee.params.map Prod.fst).length = xs'.length := by simp [xs', hlen]
      refine ⟨Nat.le_trans hxs.1 (Nat.le_succ _), fun v hv => ?_, fun v hv => ?_⟩
      · rcases hasFreeVar_bindParams (inlinePfx c1) (callee.params.map Prod.fst) xs'
          (prefixExpr (inlinePfx c1) (callee.params.map Prod.fst) callee.body) v hlen' hv with h1 | ⟨hnot, h2⟩
        · exact hxs.2.1 v h1
        · obtain ⟨u, hu, rfl, _⟩ := hasFreeVar_prefixExpr_closed (inlinePfx c1)
            (callee.params.map Prod.fst) callee.body (hclosed nm callee hl) v h2
          exact absurd (List.mem_map.mpr ⟨u, hu, rfl⟩) hnot
      · rcases hasBoundVar_bindParams (inlinePfx c1) (callee.params.map Prod.fst) xs'
          (prefixExpr (inlinePfx c1) (callee.params.map Prod.fst) callee.body) v hlen' hv with h1 | h2 | h3
        · obtain ⟨u, _, rfl⟩ := List.mem_map.mp h1
          exact Or.inr ⟨c1, u, hxs.1, Nat.lt_succ_self c1, rfl⟩
        · rcases hxs.2.2 v h2 with h2' | ⟨k, u, hk1, hk2, rfl⟩
          · exact Or.inl h2'
          · exact Or.inr ⟨k, u, hk1, Nat.lt_succ_of_lt hk2, rfl⟩
        · obtain ⟨u, rfl, _⟩ := hasBoundVar_prefixExpr (inlinePfx c1)
            (callee.params.map Prod.fst) callee.body v h3
          exact Or.inr ⟨c1, u, hxs.1, Nat.lt_succ_self c1, rfl⟩
termination_by e _ => sizeOf e

theorem inlineCallsListM_vars {imap : List (String × Fn)}
    (hclosed : ∀ nm callee, imap.lookup nm = some callee →
      ∀ u, hasFreeVar u callee.body = true → u ∈ callee.params.map Prod.fst) :
    ∀ (xs : List Expr) (c : Nat),
      c ≤ ((inlineCallsListM imap xs).run c).2 ∧
      (∀ v, hasFreeVarList v ((inlineCallsListM imap xs).run c).1 = true → hasFreeVarList v xs = true) ∧
      (∀ v, hasBoundVarList v ((inlineCallsListM imap xs).run c).1 = true →
        hasBoundVarList v xs = true ∨
        ∃ k u, c ≤ k ∧ k < ((inlineCallsListM imap xs).run c).2 ∧ v = inlinePfx k ++ u)
  | [], c => ⟨Nat.le_refl c, fun _ h => h, fun _ h => Or.inl h⟩
  | x :: xs, c => by
    have hx := inlineCallsM_vars hclosed x c
    have hxs := inlineCallsListM_vars hclosed xs ((inlineCallsM imap x).run c).2
    rw [inlineCallsListM_run_cons]
    refine ⟨Nat.le_trans hx.1 hxs.1, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [hasFreeVarList, Bool.or_eq_true] at hv ⊢
      rcases hv with h1 | h2
      · exact Or.inl (hx.2.1 v h1)
      · exact Or.inr (hxs.2.1 v h2)
    · simp only [hasBoundVarList, Bool.or_eq_true] at hv ⊢
      rcases hv with h1 | h2
      · rcases hx.2.2 v h1 with h1' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inl h1')
        · exact Or.inr ⟨k, u, hk1, lt_of_lt_of_le hk2 hxs.1, rfl⟩
      · rcases hxs.2.2 v h2 with h2' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inr h2')
        · exact Or.inr ⟨k, u, Nat.le_trans hx.1 hk1, hk2, rfl⟩
termination_by xs _ => sizeOf xs

theorem inlineCallsArmsM_vars {imap : List (String × Fn)}
    (hclosed : ∀ nm callee, imap.lookup nm = some callee →
      ∀ u, hasFreeVar u callee.body = true → u ∈ callee.params.map Prod.fst) :
    ∀ (arms : List (Pat × Expr)) (c : Nat),
      c ≤ ((inlineCallsArmsM imap arms).run c).2 ∧
      (∀ v, hasFreeVarArms v ((inlineCallsArmsM imap arms).run c).1 = true → hasFreeVarArms v arms = true) ∧
      (∀ v, hasBoundVarArms v ((inlineCallsArmsM imap arms).run c).1 = true →
        hasBoundVarArms v arms = true ∨
        ∃ k u, c ≤ k ∧ k < ((inlineCallsArmsM imap arms).run c).2 ∧ v = inlinePfx k ++ u)
  | [], c => ⟨Nat.le_refl c, fun _ h => h, fun _ h => Or.inl h⟩
  | (p, b) :: rest, c => by
    have hb := inlineCallsM_vars hclosed b c
    have hrest := inlineCallsArmsM_vars hclosed rest ((inlineCallsM imap b).run c).2
    rw [inlineCallsArmsM_run_cons]
    refine ⟨Nat.le_trans hb.1 hrest.1, fun v hv => ?_, fun v hv => ?_⟩
    · simp only [hasFreeVarArms, Bool.or_eq_true, Bool.and_eq_true] at hv ⊢
      rcases hv with ⟨hnot, h1⟩ | h2
      · exact Or.inl ⟨hnot, hb.2.1 v h1⟩
      · exact Or.inr (hrest.2.1 v h2)
    · simp only [hasBoundVarArms, Bool.or_eq_true] at hv ⊢
      rcases hv with (h0 | h1) | h2
      · exact Or.inl (Or.inl (Or.inl h0))
      · rcases hb.2.2 v h1 with h1' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inl (Or.inr h1'))
        · exact Or.inr ⟨k, u, hk1, lt_of_lt_of_le hk2 hrest.1, rfl⟩
      · rcases hrest.2.2 v h2 with h2' | ⟨k, u, hk1, hk2, rfl⟩
        · exact Or.inl (Or.inr h2')
        · exact Or.inr ⟨k, u, Nat.le_trans hb.1 hk1, hk2, rfl⟩
termination_by arms _ => sizeOf arms

end

theorem exprNoPrefixGe_inlineCallsM {imap : List (String × Fn)}
    (hclosed : ∀ nm callee, imap.lookup nm = some callee →
      ∀ u, hasFreeVar u callee.body = true → u ∈ callee.params.map Prod.fst)
    {e : Expr} {c : Nat} (hnp : ExprNoPrefixGe c e) :
    ExprNoPrefixGe ((inlineCallsM imap e).run c).2 ((inlineCallsM imap e).run c).1 := by
  obtain ⟨hle, hfv, hbv⟩ := inlineCallsM_vars hclosed e c
  refine ⟨fun v hv => (hnp.1 v (hfv v hv)).mono hle, fun v hv => ?_⟩
  rcases hbv v hv with h1 | ⟨k, u, _, hk, rfl⟩
  · exact (hnp.2 v h1).mono hle
  · exact noPrefixGe_inlinePfx_lt hk u

theorem listNoPrefixGe_inlineCallsListM {imap : List (String × Fn)}
    (hclosed : ∀ nm callee, imap.lookup nm = some callee →
      ∀ u, hasFreeVar u callee.body = true → u ∈ callee.params.map Prod.fst)
    {xs : List Expr} {c : Nat} (hnp : ListNoPrefixGe c xs) :
    ListNoPrefixGe ((inlineCallsListM imap xs).run c).2 ((inlineCallsListM imap xs).run c).1 := by
  obtain ⟨hle, hfv, hbv⟩ := inlineCallsListM_vars hclosed xs c
  refine ⟨fun v hv => (hnp.1 v (hfv v hv)).mono hle, fun v hv => ?_⟩
  rcases hbv v hv with h1 | ⟨k, u, _, hk, rfl⟩
  · exact (hnp.2 v h1).mono hle
  · exact noPrefixGe_inlinePfx_lt hk u

private theorem inlineMapValid_closed {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ nm callee, imap.lookup nm = some callee →
      ∀ u, hasFreeVar u callee.body = true → u ∈ callee.params.map Prod.fst :=
  fun nm callee hl u hu => hasFreeVar_of_hasTy (hvalid.mem nm callee hl).2.2.2.2.2.2.2.1 u hu

mutual

/-- Typing preservation for `inlineCallsM`! -/
theorem hasTy_inlineCallsM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {Γ : TyEnv} {e : Expr} {t : Lower.Ty} (c : Nat),
      ExprNoPrefixGe c e →
      HasTy sigs enums Γ e t →
      HasTy sigs enums Γ ((inlineCallsM imap e).run c).1 t
  | _, _, _, _, _, .literal => .literal
  | _, _, _, _, _, .var hl => .var hl
  | _, _, _, c, hnp, .tuple items => by
    rw [inlineCallsM_run_tuple]; exact .tuple (hasTyList_inlineCallsListM hvalid c hnp items)
  | _, _, _, c, hnp, .array hlen items => by
    rw [inlineCallsM_run_array]
    exact .array (by rw [inlineCallsListM_length]; exact hlen) (hasTyList_inlineCallsListM hvalid c hnp items)
  | _, _, _, c, hnp, .repeat hx => by
    rw [inlineCallsM_run_repeat]; exact .repeat (hasTy_inlineCallsM hvalid c hnp hx)
  | _, _, _, c, hnp, .index hx => by
    rw [inlineCallsM_run_index]; exact .index (hasTy_inlineCallsM hvalid c hnp hx)
  | _, _, _, c, hnp, .project hx hget => by
    rw [inlineCallsM_run_project]; exact .project (hasTy_inlineCallsM hvalid c hnp hx) hget
  | _, _, _, c, hnp, .slice hnot hx => by
    rw [inlineCallsM_run_slice]; exact .slice hnot (hasTy_inlineCallsM hvalid c hnp hx)
  | _, _, _, c, hnp, .construct h1 h2 h3 h4 hctor items => by
    rw [inlineCallsM_run_construct]; exact .construct h1 h2 h3 h4 hctor (hasTyList_inlineCallsListM hvalid c hnp items)
  | _, _, _, c, hnp, .builtin items => by
    rw [inlineCallsM_run_builtin]; exact .builtin (hasTyList_inlineCallsListM hvalid c hnp items)
  | _, _, _, c, hnp, .store hx => by
    rw [inlineCallsM_run_store]; exact .store (hasTy_inlineCallsM hvalid c hnp hx)
  | _, _, _, c, hnp, .load hx => by
    rw [inlineCallsM_run_load]; exact .load (hasTy_inlineCallsM hvalid c hnp hx)
  | _, _, _, c, hnp, .hint hfo hx => by
    rw [inlineCallsM_run_hint]; exact .hint hfo (hasTy_inlineCallsM hvalid c hnp hx)
  | _, _, _, c, hnp, .neg hx => by
    rw [inlineCallsM_run_neg]; exact .neg (hasTy_inlineCallsM hvalid c hnp hx)
  | _, .binary _ l r, _, c, hnp, .binary hl hr => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl l c).1
    have hnpL : ExprNoPrefixGe c l :=
      ⟨fun v hv => hnp.1 v (by simp [hasFreeVar, hv]), fun v hv => hnp.2 v (by simp [hasBoundVar, hv])⟩
    have hnpR : ExprNoPrefixGe ((inlineCallsM imap l).run c).2 r :=
      (ExprNoPrefixGe.mono hle
        ⟨fun v hv => hnp.1 v (by simp [hasFreeVar, hv]), fun v hv => hnp.2 v (by simp [hasBoundVar, hv])⟩)
    rw [inlineCallsM_run_binary]
    exact .binary (hasTy_inlineCallsM hvalid c hnpL hl) (hasTy_inlineCallsM hvalid _ hnpR hr)
  | _, .letValue _ v b, _, c, hnp, .letValue hx hp hb => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl v c).1
    rw [inlineCallsM_run_letValue]
    exact .letValue (hasTy_inlineCallsM hvalid c (exprNoPrefixGe_letValue_rhs hnp) hx) hp
      (hasTy_inlineCallsM hvalid _ ((exprNoPrefixGe_letValue_body hnp).mono hle) hb)
  | _, .matchValue s _, _, c, hnp, .matchValue hs harms => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl s c).1
    rw [inlineCallsM_run_matchValue]
    exact .matchValue (hasTy_inlineCallsM hvalid c (exprNoPrefixGe_matchValue_scrut hnp) hs)
      (hasTyArms_inlineCallsArmsM hvalid _ ((armsNoPrefixGe_matchValue hnp).mono hle) harms)
  | Γ, .call nm (some []) xs, t, c, hnp, .call (ptys := ptys) hsig items => by
    have hcl := inlineMapValid_closed hvalid
    have hxsVars := inlineCallsListM_vars hcl xs c
    have hxsTy := hasTyList_inlineCallsListM hvalid c hnp items
    rcases inlineCallsM_run_call_cases imap nm (some []) xs c with hno | ⟨callee, _, hl, _, hres⟩
    · rw [hno]; exact .call hsig hxsTy
    · rw [hres]
      obtain ⟨_, _, _, hnoCol, hdist, hsigCal, _, htyCal, _, _, _⟩ := hvalid.mem nm callee hl
      have hq : qualifyName nm = qualified nm := by simp [qualifyName, hnoCol]
      rw [hq, hsigCal, Option.some.injEq, Prod.mk.injEq] at hsig
      obtain ⟨rfl, rfl⟩ := hsig
      let c1 := ((inlineCallsListM imap xs).run c).2
      let xs' := ((inlineCallsListM imap xs).run c).1
      have hnd : (callee.params.map Prod.fst).Nodup := nodup_of_allDistinct hdist
      have hndPref : ((callee.params.map fun q => (inlinePfx c1 ++ q.1, q.2)).map Prod.fst).Nodup := by
        rw [List.map_map]
        have : (Prod.fst ∘ fun q : String × Lower.Ty => (inlinePfx c1 ++ q.1, q.2)) =
            (inlinePfx c1 ++ ·) ∘ Prod.fst := rfl
        rw [this, ← List.map_map]
        exact hnd.map fun _ _ heq => string_append_left_inj heq
      refine hasTy_bindParams (inlinePfx c1) callee.params xs' Γ _ callee.result hxsTy ?_ ?_
      · intro p _
        cases hf : hasFreeVarList (inlinePfx c1 ++ p) xs' with
        | false => rfl
        | true =>
          have hfOrig := hxsVars.2.1 _ hf
          exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnp.1 _ hfOrig) hxsVars.1 p)
      · refine hasTy_prefixExpr (inlinePfx c1) (callee.params.map Prod.fst) htyCal fun x hfx => ?_
        have hxMem : x ∈ callee.params.map Prod.fst := hasFreeVar_of_hasTy htyCal x hfx
        refine ⟨hxMem, ?_⟩
        have hmemRev : inlinePfx c1 ++ x ∈
            ((callee.params.map fun q => (inlinePfx c1 ++ q.1, q.2)).reverse).map Prod.fst := by
          rw [List.map_reverse]; exact List.mem_reverse.mpr (by
            rw [List.map_map]; exact List.mem_map.mpr (by
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxMem; exact ⟨q, hq, rfl⟩))
        have hlookApp : (((callee.params.map fun q => (inlinePfx c1 ++ q.1, q.2)).reverse) ++ Γ).lookup
            (inlinePfx c1 ++ x) =
            ((callee.params.map fun q => (inlinePfx c1 ++ q.1, q.2)).reverse).lookup (inlinePfx c1 ++ x) :=
          lookup_append_of_mem_poly hmemRev
        rw [hlookApp, lookup_reverse_of_nodup hndPref, lookup_map_prefix]
termination_by _ e _ _ _ _ => sizeOf e

theorem hasTyList_inlineCallsListM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {Γ : TyEnv} {xs : List Expr} {ts : List Lower.Ty} (c : Nat),
      ListNoPrefixGe c xs →
      HasTyList sigs enums Γ xs ts →
      HasTyList sigs enums Γ ((inlineCallsListM imap xs).run c).1 ts
  | _, _, _, _, _, .nil => .nil
  | _, x :: xs, _, c, hnp, .cons hd tl => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl x c).1
    have hnpH : ExprNoPrefixGe c x :=
      ⟨fun v hv => hnp.1 v (by simp [hasFreeVarList, hv]), fun v hv => hnp.2 v (by simp [hasBoundVarList, hv])⟩
    have hnpT : ListNoPrefixGe ((inlineCallsM imap x).run c).2 xs :=
      (ListNoPrefixGe.mono hle
        ⟨fun v hv => hnp.1 v (by simp [hasFreeVarList, hv]), fun v hv => hnp.2 v (by simp [hasBoundVarList, hv])⟩)
    rw [inlineCallsListM_run_cons]
    exact .cons (hasTy_inlineCallsM hvalid c hnpH hd) (hasTyList_inlineCallsListM hvalid _ hnpT tl)
termination_by _ xs _ _ _ _ => sizeOf xs

theorem hasTyArms_inlineCallsArmsM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {Γ : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)} (c : Nat),
      ArmsNoPrefixGe c arms →
      HasTyArms sigs enums Γ ts arms tb →
      HasTyArms sigs enums Γ ts ((inlineCallsArmsM imap arms).run c).1 tb
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, (_, b) :: _, c, hnp, .cons hp hb tl => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl b c).1
    rw [inlineCallsArmsM_run_cons]
    exact .cons hp (hasTy_inlineCallsM hvalid c (exprNoPrefixGe_arm_body hnp) hb)
      (hasTyArms_inlineCallsArmsM hvalid _ ((armsNoPrefixGe_tail hnp).mono hle) tl)
termination_by _ _ _ arms _ _ _ => sizeOf arms

end

mutual

/-- `NoLetShadow` preservation for `inlineCallsM`! -/
theorem noLetShadow_inlineCallsM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {scope : List String} {e : Expr} (c : Nat),
      (∀ s ∈ scope, NoPrefixGe c s) →
      ExprNoPrefixGe c e →
      NoLetShadow scope e →
      NoLetShadow scope ((inlineCallsM imap e).run c).1
  | _, .literal _, _, _, _, _ | _, .var _, _, _, _, _ | _, .global _ _, _, _, _, _
  | _, .control _ _, _, _, _, _ => trivial
  | _, .tuple xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_tuple]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .array xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_array]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .construct _ _ _ xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_construct]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .constructAs _ _ _ xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_constructAs]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .record _ xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_record]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .update _ xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_update]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .builtin _ xs, c, hsc, hnp, hns => by rw [inlineCallsM_run_builtin]; exact noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
  | _, .repeat x _, c, hsc, hnp, hns => by rw [inlineCallsM_run_repeat]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .index x _, c, hsc, hnp, hns => by rw [inlineCallsM_run_index]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .slice x _ _, c, hsc, hnp, hns => by rw [inlineCallsM_run_slice]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .member x _, c, hsc, hnp, hns => by rw [inlineCallsM_run_member]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .project x _, c, hsc, hnp, hns => by rw [inlineCallsM_run_project]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .store x, c, hsc, hnp, hns => by rw [inlineCallsM_run_store]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .load x, c, hsc, hnp, hns => by rw [inlineCallsM_run_load]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .hint _ x _, c, hsc, hnp, hns => by rw [inlineCallsM_run_hint]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | _, .neg x, c, hsc, hnp, hns => by rw [inlineCallsM_run_neg]; exact noLetShadow_inlineCallsM hvalid c hsc hnp hns
  | scope, .binary _ l r, c, hsc, hnp, ⟨hdisj, hl, hr⟩ => by
    have hcl := inlineMapValid_closed hvalid
    have hlV := inlineCallsM_vars hcl l c
    have hrV := inlineCallsM_vars hcl r ((inlineCallsM imap l).run c).2
    have hnpL : ExprNoPrefixGe c l :=
      ⟨fun v hv => hnp.1 v (by simp [hasFreeVar, hv]), fun v hv => hnp.2 v (by simp [hasBoundVar, hv])⟩
    have hnpR : ExprNoPrefixGe ((inlineCallsM imap l).run c).2 r :=
      (ExprNoPrefixGe.mono hlV.1
        ⟨fun v hv => hnp.1 v (by simp [hasFreeVar, hv]), fun v hv => hnp.2 v (by simp [hasBoundVar, hv])⟩)
    rw [inlineCallsM_run_binary]
    refine ⟨fun v hv => ?_,
      noLetShadow_inlineCallsM hvalid c hsc hnpL hl,
      noLetShadow_inlineCallsM hvalid _ (fun s hs => (hsc s hs).mono hlV.1) hnpR hr⟩
    cases hrb : hasBoundVar v ((inlineCallsM imap r).run ((inlineCallsM imap l).run c).2).1 with
    | false => rfl
    | true =>
      rcases hlV.2.2 v hv with h1 | ⟨k1, u1, hk1, hk1', rfl⟩
      · rcases hrV.2.2 v hrb with h2 | ⟨k2, u2, hk2, _, rfl⟩
        · rw [hdisj v h1] at h2; cases h2
        · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnpL.2 _ h1) (Nat.le_trans hlV.1 hk2) u2)
      · rcases hrV.2.2 _ hrb with h2 | ⟨k2, u2, hk2, _, heq⟩
        · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnp.2 _ (by simp [hasBoundVar, h2])) hk1 u1)
        · obtain ⟨rfl, _⟩ := inlinePfx_inj heq; omega
  | scope, .letValue p x b, c, hsc, hnp, ⟨hp, hdisj, hx, hb⟩ => by
    have hcl := inlineMapValid_closed hvalid
    have hxV := inlineCallsM_vars hcl x c
    have hbV := inlineCallsM_vars hcl b ((inlineCallsM imap x).run c).2
    have hnpX := exprNoPrefixGe_letValue_rhs hnp
    have hnpB := (exprNoPrefixGe_letValue_body hnp).mono hxV.1
    rw [inlineCallsM_run_letValue]
    refine ⟨hp, fun v hv => ?_, noLetShadow_inlineCallsM hvalid c hsc hnpX hx,
      noLetShadow_inlineCallsM hvalid _ (fun s hs => ?_) hnpB hb⟩
    · refine ⟨fun hmem => ?_, ?_⟩
      · rcases hxV.2.2 v hv with h1 | ⟨k, u, hk, _, rfl⟩
        · exact (hdisj v h1).1 hmem
        · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnp.2 _ (by simp [hasBoundVar, hmem])) hk u)
      · cases hbb : hasBoundVar v ((inlineCallsM imap b).run ((inlineCallsM imap x).run c).2).1 with
        | false => rfl
        | true =>
          rcases hxV.2.2 v hv with h1 | ⟨k1, u1, hk1, hk1', rfl⟩
          · rcases hbV.2.2 v hbb with h2 | ⟨k2, u2, hk2, _, rfl⟩
            · rw [(hdisj v h1).2] at h2; cases h2
            · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnpX.2 _ h1) (Nat.le_trans hxV.1 hk2) u2)
          · rcases hbV.2.2 _ hbb with h2 | ⟨k2, u2, hk2, _, heq⟩
            · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnp.2 _ (by simp [hasBoundVar, h2])) hk1 u1)
            · obtain ⟨rfl, _⟩ := inlinePfx_inj heq; omega
    · rcases List.mem_append.mp hs with h1 | h2
      · exact (hnp.2 s (by simp [hasBoundVar, h1])).mono hxV.1
      · exact (hsc s h2).mono hxV.1
  | scope, .matchValue s arms, c, hsc, hnp, ⟨hs, harms⟩ => by
    have hcl := inlineMapValid_closed hvalid
    have hsV := inlineCallsM_vars hcl s c
    rw [inlineCallsM_run_matchValue]
    exact ⟨noLetShadow_inlineCallsM hvalid c hsc (exprNoPrefixGe_matchValue_scrut hnp) hs,
      noLetShadowArms_inlineCallsArmsM hvalid _ (fun x hx => (hsc x hx).mono hsV.1)
        ((armsNoPrefixGe_matchValue hnp).mono hsV.1) harms⟩
  | scope, .call nm targs xs, c, hsc, hnp, hns => by
    have hcl := inlineMapValid_closed hvalid
    have hxsV := inlineCallsListM_vars hcl xs c
    have hnsXs := noLetShadowList_inlineCallsListM hvalid c hsc hnp hns
    have hnpXs' := listNoPrefixGe_inlineCallsListM hcl hnp
    rcases inlineCallsM_run_call_cases imap nm targs xs c with hno | ⟨callee, _, hl, hlen, hres⟩
    · rw [hno]; exact hnsXs
    · rw [hres]
      obtain ⟨_, _, _, _, hdist, _, _, _, hnsCal, _, _⟩ := hvalid.mem nm callee hl
      let c1 := ((inlineCallsListM imap xs).run c).2
      let xs' := ((inlineCallsListM imap xs).run c).1
      refine noLetShadow_bindParams (inlinePfx c1) (callee.params.map Prod.fst) xs'
        (prefixExpr (inlinePfx c1) (callee.params.map Prod.fst) callee.body) scope
        (by simp [xs', hlen]) (nodup_of_allDistinct hdist) hnsXs ?_ ?_ ?_
      · intro s hs p _
        exact ne_inlinePfx_of_noPrefixGe ((hsc s hs).mono hxsV.1) (Nat.le_refl c1) p
      · intro v hv
        refine ⟨fun p _ => ne_inlinePfx_of_noPrefixGe (hnpXs'.2 v hv) (Nat.le_refl c1) p, ?_⟩
        cases hrb : hasBoundVar v (prefixExpr (inlinePfx c1) (callee.params.map Prod.fst) callee.body) with
        | false => rfl
        | true =>
          obtain ⟨u, rfl, _⟩ := hasBoundVar_prefixExpr (inlinePfx c1) _ callee.body v hrb
          exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnpXs'.2 _ hv) (Nat.le_refl c1) u)
      · exact noLetShadow_prefixExpr (inlinePfx c1) scope (callee.params.map Prod.fst) hnsCal
          (fun u _ hmem => absurd rfl (ne_inlinePfx_of_noPrefixGe ((hsc _ hmem).mono hxsV.1) (Nat.le_refl c1) u))
termination_by _ e _ _ _ _ => sizeOf e

theorem noLetShadowList_inlineCallsListM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {scope : List String} {xs : List Expr} (c : Nat),
      (∀ s ∈ scope, NoPrefixGe c s) →
      ListNoPrefixGe c xs →
      NoLetShadowList scope xs →
      NoLetShadowList scope ((inlineCallsListM imap xs).run c).1
  | _, [], _, _, _, _ => trivial
  | scope, x :: xs, c, hsc, hnp, ⟨hdisj, hx, hxs⟩ => by
    have hcl := inlineMapValid_closed hvalid
    have hxV := inlineCallsM_vars hcl x c
    have hxsV := inlineCallsListM_vars hcl xs ((inlineCallsM imap x).run c).2
    have hnpX : ExprNoPrefixGe c x :=
      ⟨fun v hv => hnp.1 v (by simp [hasFreeVarList, hv]), fun v hv => hnp.2 v (by simp [hasBoundVarList, hv])⟩
    have hnpXs : ListNoPrefixGe ((inlineCallsM imap x).run c).2 xs :=
      (ListNoPrefixGe.mono hxV.1
        ⟨fun v hv => hnp.1 v (by simp [hasFreeVarList, hv]), fun v hv => hnp.2 v (by simp [hasBoundVarList, hv])⟩)
    rw [inlineCallsListM_run_cons]
    refine ⟨fun v hv => ?_,
      noLetShadow_inlineCallsM hvalid c hsc hnpX hx,
      noLetShadowList_inlineCallsListM hvalid _ (fun s hs => (hsc s hs).mono hxV.1) hnpXs hxs⟩
    cases hrb : hasBoundVarList v ((inlineCallsListM imap xs).run ((inlineCallsM imap x).run c).2).1 with
    | false => rfl
    | true =>
      rcases hxV.2.2 v hv with h1 | ⟨k1, u1, hk1, hk1', rfl⟩
      · rcases hxsV.2.2 v hrb with h2 | ⟨k2, u2, hk2, _, rfl⟩
        · rw [hdisj v h1] at h2; cases h2
        · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnpX.2 _ h1) (Nat.le_trans hxV.1 hk2) u2)
      · rcases hxsV.2.2 _ hrb with h2 | ⟨k2, u2, hk2, _, heq⟩
        · exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnp.2 _ (by simp [hasBoundVarList, h2])) hk1 u1)
        · obtain ⟨rfl, _⟩ := inlinePfx_inj heq; omega
termination_by _ xs _ _ _ _ => sizeOf xs

theorem noLetShadowArms_inlineCallsArmsM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {scope : List String} {arms : List (Pat × Expr)} (c : Nat),
      (∀ s ∈ scope, NoPrefixGe c s) →
      ArmsNoPrefixGe c arms →
      NoLetShadowArms scope arms →
      NoLetShadowArms scope ((inlineCallsArmsM imap arms).run c).1
  | _, [], _, _, _, _ => trivial
  | scope, (p, b) :: rest, c, hsc, hnp, ⟨hp, hb, hrest⟩ => by
    have hcl := inlineMapValid_closed hvalid
    have hbV := inlineCallsM_vars hcl b c
    rw [inlineCallsArmsM_run_cons]
    refine ⟨hp, noLetShadow_inlineCallsM hvalid c (fun s hs => ?_) (exprNoPrefixGe_arm_body hnp) hb,
      noLetShadowArms_inlineCallsArmsM hvalid _ (fun s hs => (hsc s hs).mono hbV.1)
        ((armsNoPrefixGe_tail hnp).mono hbV.1) hrest⟩
    rcases List.mem_append.mp hs with h1 | h2
    · exact hnp.2 s (by simp [hasBoundVarArms, h1])
    · exact hsc s h2
termination_by _ arms _ _ _ _ => sizeOf arms

end

mutual

/-- `literalsBounded` and `noInlinableInBoundedCalls` preservation for `inlineCallsM`! -/
theorem literalsBounded_inlineCallsM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {e : Expr} (c : Nat),
      literalsBounded e = true →
      noInlinableInBoundedCalls e = true →
      literalsBounded ((inlineCallsM imap e).run c).1 = true ∧
      noInlinableInBoundedCalls ((inlineCallsM imap e).run c).1 = true
  | .literal _, _, _, _ | .var _, _, _, _ | .global _ _, _, _, _ => ⟨rfl, rfl⟩
  | .control _ _, _, hlb, hni => ⟨hlb, hni⟩
  | .tuple xs, c, hlb, hni => by rw [inlineCallsM_run_tuple]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .array xs, c, hlb, hni => by rw [inlineCallsM_run_array]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .construct _ _ _ xs, c, hlb, hni => by rw [inlineCallsM_run_construct]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .constructAs _ _ _ xs, c, hlb, hni => by rw [inlineCallsM_run_constructAs]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .record _ xs, c, hlb, hni => by rw [inlineCallsM_run_record]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .update _ xs, c, hlb, hni => by rw [inlineCallsM_run_update]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .builtin _ xs, c, hlb, hni => by rw [inlineCallsM_run_builtin]; exact literalsBoundedList_inlineCallsListM hvalid c hlb hni
  | .repeat x _, c, hlb, hni => by rw [inlineCallsM_run_repeat]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .index x _, c, hlb, hni => by rw [inlineCallsM_run_index]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .slice x _ _, c, hlb, hni => by rw [inlineCallsM_run_slice]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .member x _, c, hlb, hni => by rw [inlineCallsM_run_member]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .project x _, c, hlb, hni => by rw [inlineCallsM_run_project]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .store x, c, hlb, hni => by rw [inlineCallsM_run_store]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .load x, c, hlb, hni => by rw [inlineCallsM_run_load]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .hint _ x _, c, hlb, hni => by rw [inlineCallsM_run_hint]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .neg x, c, hlb, hni => by rw [inlineCallsM_run_neg]; exact literalsBounded_inlineCallsM hvalid c (e := x) hlb hni
  | .binary _ l r, c, hlb, hni => by
    simp only [literalsBounded, noInlinableInBoundedCalls, Bool.and_eq_true] at hlb hni
    rw [inlineCallsM_run_binary]
    have hl := literalsBounded_inlineCallsM hvalid c hlb.1 hni.1
    have hr := literalsBounded_inlineCallsM hvalid ((inlineCallsM imap l).run c).2 hlb.2 hni.2
    simp only [literalsBounded, noInlinableInBoundedCalls, Bool.and_eq_true]
    exact ⟨⟨hl.1, hr.1⟩, ⟨hl.2, hr.2⟩⟩
  | .letValue _ v b, c, hlb, hni => by
    simp only [literalsBounded, noInlinableInBoundedCalls, Bool.and_eq_true] at hlb hni
    rw [inlineCallsM_run_letValue]
    have hv := literalsBounded_inlineCallsM hvalid c hlb.1 hni.1
    have hb := literalsBounded_inlineCallsM hvalid ((inlineCallsM imap v).run c).2 hlb.2 hni.2
    simp only [literalsBounded, noInlinableInBoundedCalls, Bool.and_eq_true]
    exact ⟨⟨hv.1, hb.1⟩, ⟨hv.2, hb.2⟩⟩
  | .matchValue s arms, c, hlb, hni => by
    simp only [literalsBounded, noInlinableInBoundedCalls, Bool.and_eq_true] at hlb hni
    rw [inlineCallsM_run_matchValue]
    have hs := literalsBounded_inlineCallsM hvalid c hlb.1 hni.1
    have ha := literalsBoundedArms_inlineCallsArmsM hvalid ((inlineCallsM imap s).run c).2 hlb.2 hni.2
    simp only [literalsBounded, noInlinableInBoundedCalls, Bool.and_eq_true]
    exact ⟨⟨hs.1, ha.1⟩, ⟨hs.2, ha.2⟩⟩
  | .call nm targs xs, c, hlb, hni => by
    have hnames : ∀ nm' cal, imap.lookup nm' = some cal → (nm'.startsWith "f" || nm'.startsWith "jp") = true :=
      fun nm' cal hl => (hvalid.mem nm' cal hl).2.2.1
    have hxs := literalsBoundedList_inlineCallsListM hvalid c (literalsBounded_call_args hlb)
      (noInlinableInBoundedCalls_call_args hni)
    cases targs with
    | none => rw [inlineCallsM_run_call_none]; exact hxs
    | some ts =>
      cases ts with
      | cons _ _ => rw [inlineCallsM_run_call_cons]; exact hxs
      | nil =>
        cases hl : imap.lookup nm with
        | some callee =>
          by_cases hlen : callee.params.length = ((inlineCallsListM imap xs).run c).1.length
          · rw [inlineCallsM_run_call_inline imap nm xs c callee hl hlen]
            obtain ⟨_, _, _, _, _, _, _, _, _, hlbCal, hniCal⟩ := hvalid.mem nm callee hl
            refine ⟨literalsBounded_bindParams _ _ _ _ (by simp [hlen]) hxs.1
                (by rw [literalsBounded_prefixExpr]; exact hlbCal),
              noInlinableInBoundedCalls_bindParams _ _ _ _ (by simp [hlen]) hxs.2
                (by rw [noInlinableInBoundedCalls_prefixExpr]; exact hniCal)⟩
          · rw [inlineCallsM_run_call_len_ne imap nm xs c callee hl hlen]
            cases xs with
            | nil => exact ⟨rfl, rfl⟩
            | cons x rest =>
              cases rest with
              | cons y rest2 => exact hxs
              | nil =>
                have hnotB : (nm == "u32_of_field" || nm == "Prog::u32_of_field" || nm == "UInt32::from_field") = false := by
                  have hst := hnames nm callee hl
                  have h1 : (nm == "u32_of_field") = false := by
                    cases hc : (nm == "u32_of_field"); · rfl
                    simp only [beq_iff_eq] at hc; subst hc; simp at hst
                  have h2 : (nm == "Prog::u32_of_field") = false := by
                    cases hc : (nm == "Prog::u32_of_field"); · rfl
                    simp only [beq_iff_eq] at hc; subst hc; simp at hst
                  have h3 : (nm == "UInt32::from_field") = false := by
                    cases hc : (nm == "UInt32::from_field"); · rfl
                    simp only [beq_iff_eq] at hc; subst hc; simp at hst
                  simp [h1, h2, h3]
                simp only [Bool.or_eq_false_iff] at hnotB
                have hx1 := literalsBounded_inlineCallsM hvalid c
                  (by simpa [literalsBounded, hnotB.1.1, hnotB.1.2, hnotB.2] using hlb)
                  (by simpa [noInlinableInBoundedCalls, hnotB.1.1, hnotB.1.2, hnotB.2] using hni)
                rw [inlineCallsListM_run_cons, inlineCallsListM_run_nil]
                simpa [literalsBounded, noInlinableInBoundedCalls, hnotB.1.1, hnotB.1.2, hnotB.2] using hx1
        | none =>
          rw [inlineCallsM_run_call_lookup_none imap nm xs c hl]
          cases xs with
          | nil => exact ⟨rfl, rfl⟩
          | cons x rest =>
            cases rest with
            | cons y rest2 => exact hxs
            | nil =>
              rw [inlineCallsListM_run_cons, inlineCallsListM_run_nil]
              cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
              | true =>
                have hniX : noInlinableCalls x = true := by
                  simpa [noInlinableInBoundedCalls, h1] using hni
                rw [inlineCallsM_of_noInlinableCalls hnames c hniX]
                exact ⟨hlb, hni⟩
              | false =>
                cases h2 : (nm == "UInt32::from_field") with
                | true =>
                  have hniX : noInlinableCalls x = true := by
                    simpa [noInlinableInBoundedCalls, h1, h2] using hni
                  rw [inlineCallsM_of_noInlinableCalls hnames c hniX]
                  exact ⟨hlb, hni⟩
                | false =>
                  have hlbX : literalsBounded x = true := by
                    simpa [literalsBounded, h1, h2] using hlb
                  have hniX : noInlinableInBoundedCalls x = true := by
                    simpa [noInlinableInBoundedCalls, h1, h2] using hni
                  have hx' := literalsBounded_inlineCallsM hvalid c hlbX hniX
                  simpa [literalsBounded, noInlinableInBoundedCalls, h1, h2] using hx'
termination_by e _ _ _ => sizeOf e
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem literalsBoundedList_inlineCallsListM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {xs : List Expr} (c : Nat),
      literalsBoundedList xs = true →
      noInlinableInBoundedCallsList xs = true →
      literalsBoundedList ((inlineCallsListM imap xs).run c).1 = true ∧
      noInlinableInBoundedCallsList ((inlineCallsListM imap xs).run c).1 = true
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, c, hlb, hni => by
    simp only [literalsBoundedList, noInlinableInBoundedCallsList, Bool.and_eq_true] at hlb hni
    rw [inlineCallsListM_run_cons]
    have hx := literalsBounded_inlineCallsM hvalid c hlb.1 hni.1
    have hxs := literalsBoundedList_inlineCallsListM hvalid ((inlineCallsM imap x).run c).2 hlb.2 hni.2
    simp only [literalsBoundedList, noInlinableInBoundedCallsList, Bool.and_eq_true]
    exact ⟨⟨hx.1, hxs.1⟩, ⟨hx.2, hxs.2⟩⟩
termination_by xs _ _ _ => sizeOf xs

theorem literalsBoundedArms_inlineCallsArmsM {F : Type} [Field F] [DecidableEq F]
    {world : World F} {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {arms : List (Pat × Expr)} (c : Nat),
      literalsBoundedArms arms = true →
      noInlinableInBoundedCallsArms arms = true →
      literalsBoundedArms ((inlineCallsArmsM imap arms).run c).1 = true ∧
      noInlinableInBoundedCallsArms ((inlineCallsArmsM imap arms).run c).1 = true
  | [], _, _, _ => ⟨rfl, rfl⟩
  | (p, b) :: rest, c, hlb, hni => by
    simp only [literalsBoundedArms, noInlinableInBoundedCallsArms, Bool.and_eq_true] at hlb hni
    rw [inlineCallsArmsM_run_cons]
    have hb := literalsBounded_inlineCallsM hvalid c hlb.1 hni.1
    have hr := literalsBoundedArms_inlineCallsArmsM hvalid ((inlineCallsM imap b).run c).2 hlb.2 hni.2
    simp only [literalsBoundedArms, noInlinableInBoundedCallsArms, Bool.and_eq_true]
    exact ⟨⟨hb.1, hr.1⟩, ⟨hb.2, hr.2⟩⟩
termination_by arms _ _ _ => sizeOf arms

end

section InlineCallsEval

variable {F : Type} [Field F] [DecidableEq F]

private theorem inlineCallsM_counter_le_uncond (imap : List (String × Fn)) :
    ∀ (e : Expr) (c : Nat), c ≤ ((inlineCallsM imap e).run c).2
  | .literal _, c | .var _, c | .global _ _, c | .control _ _, c => Nat.le_refl c
  | .tuple xs, c => by rw [inlineCallsM_run_tuple]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .array xs, c => by rw [inlineCallsM_run_array]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .construct _ _ _ xs, c => by rw [inlineCallsM_run_construct]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .constructAs _ _ _ xs, c => by rw [inlineCallsM_run_constructAs]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .record _ xs, c => by rw [inlineCallsM_run_record]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .update _ xs, c => by rw [inlineCallsM_run_update]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .builtin _ xs, c => by rw [inlineCallsM_run_builtin]; exact inlineCallsListM_counter_le_uncond imap xs c
  | .repeat x _, c => by rw [inlineCallsM_run_repeat]; exact inlineCallsM_counter_le_uncond imap x c
  | .index x _, c => by rw [inlineCallsM_run_index]; exact inlineCallsM_counter_le_uncond imap x c
  | .slice x _ _, c => by rw [inlineCallsM_run_slice]; exact inlineCallsM_counter_le_uncond imap x c
  | .member x _, c => by rw [inlineCallsM_run_member]; exact inlineCallsM_counter_le_uncond imap x c
  | .project x _, c => by rw [inlineCallsM_run_project]; exact inlineCallsM_counter_le_uncond imap x c
  | .store x, c => by rw [inlineCallsM_run_store]; exact inlineCallsM_counter_le_uncond imap x c
  | .load x, c => by rw [inlineCallsM_run_load]; exact inlineCallsM_counter_le_uncond imap x c
  | .hint _ x _, c => by rw [inlineCallsM_run_hint]; exact inlineCallsM_counter_le_uncond imap x c
  | .neg x, c => by rw [inlineCallsM_run_neg]; exact inlineCallsM_counter_le_uncond imap x c
  | .binary _ l r, c => by
    rw [inlineCallsM_run_binary]
    exact Nat.le_trans (inlineCallsM_counter_le_uncond imap l c) (inlineCallsM_counter_le_uncond imap r _)
  | .letValue _ v b, c => by
    rw [inlineCallsM_run_letValue]
    exact Nat.le_trans (inlineCallsM_counter_le_uncond imap v c) (inlineCallsM_counter_le_uncond imap b _)
  | .matchValue s arms, c => by
    rw [inlineCallsM_run_matchValue]
    exact Nat.le_trans (inlineCallsM_counter_le_uncond imap s c) (inlineCallsArmsM_counter_le_uncond imap arms _)
  | .call nm targs xs, c => by
    have h1 := inlineCallsListM_counter_le_uncond imap xs c
    rcases inlineCallsM_run_call_cases imap nm targs xs c with hno | ⟨_, _, _, _, hres⟩
    · rw [hno]; exact h1
    · rw [hres]; exact Nat.le_trans h1 (Nat.le_succ _)
where
  inlineCallsListM_counter_le_uncond (imap : List (String × Fn)) :
      ∀ (xs : List Expr) (c : Nat), c ≤ ((inlineCallsListM imap xs).run c).2
    | [], c => Nat.le_refl c
    | x :: xs, c => by
      rw [inlineCallsListM_run_cons]
      exact Nat.le_trans (inlineCallsM_counter_le_uncond imap x c) (inlineCallsListM_counter_le_uncond imap xs _)
  inlineCallsArmsM_counter_le_uncond (imap : List (String × Fn)) :
      ∀ (arms : List (Pat × Expr)) (c : Nat), c ≤ ((inlineCallsArmsM imap arms).run c).2
    | [], c => Nat.le_refl c
    | (_, b) :: rest, c => by
      rw [inlineCallsArmsM_run_cons]
      exact Nat.le_trans (inlineCallsM_counter_le_uncond imap b c) (inlineCallsArmsM_counter_le_uncond imap rest _)

private theorem selectArm_inlineCallsArmsM {world : World F} {h : Heap F}
    {imap : List (String × Fn)} :
    ∀ {arms : List (Pat × Expr)} (c : Nat) {v : SourceValue F} {bs : Environment F Nat}
      {branch' : Aiur.Generic.Expr F},
      SourceSemantics.selectArm world [] h v
          (((inlineCallsArmsM imap arms).run c).1.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
        .ok (some (bs, branch')) →
      ∃ p b c_b, (p, b) ∈ arms ∧ c ≤ c_b ∧
        branch' = qualifyExprF F ((inlineCallsM imap b).run c_b).1 ∧
        world.matchPattern [] h (qualifyPatF F p) v = .ok (some bs) ∧
        SourceSemantics.selectArm world [] h v
          (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
          .ok (some (bs, qualifyExprF F b))
  | [], _, _, _, _, hsel => by simp [inlineCallsArmsM, StateT.run, pure, StateT.pure, SourceSemantics.selectArm, Except.pure] at hsel
  | (p, b) :: rest, c, v, bs, branch', hsel => by
    rw [inlineCallsArmsM_run_cons] at hsel
    simp only [List.map_cons, SourceSemantics.selectArm] at hsel ⊢
    cases hm : world.matchPattern [] h (qualifyPatF F p) v with
    | error err => simp [hm, bind, Except.bind] at hsel
    | ok opt =>
      cases opt with
      | none =>
        simp only [hm, bind, Except.bind] at hsel ⊢
        obtain ⟨p0, b0, cb, hmem, hle, hbr, hm0, hsel0⟩ :=
          selectArm_inlineCallsArmsM (c := ((inlineCallsM imap b).run c).2) hsel
        exact ⟨p0, b0, cb, List.mem_cons_of_mem _ hmem,
          Nat.le_trans (inlineCallsM_counter_le_uncond imap b c) hle, hbr, hm0, hsel0⟩
      | some bs0 =>
        simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
          Prod.mk.injEq] at hsel ⊢
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨p, b, c, List.mem_cons_self, Nat.le_refl c, rfl, hm, ⟨rfl, rfl⟩⟩

private theorem armsNoPrefixGe_mem {c : Nat} {arms : List (Pat × Expr)} {p : Pat} {b : Expr}
    (h : ArmsNoPrefixGe c arms) (hmem : (p, b) ∈ arms) : ExprNoPrefixGe c b := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact exprNoPrefixGe_arm_body h
    · exact ih (armsNoPrefixGe_tail h) htl

mutual

/-- **Stage 5 (`inlineCallsM`) Backward Soundness:**
Any `EvalExpr` derivation on `(inlineCallsM imap e).run c` lifts backward to `EvalExpr` on `e`
in the same world (constructing the original `EvalFn` derivations for all inlined calls)! -/
theorem evalExpr_inlineCallsM_backward {world : World F} {sigs : FnSigs}
    {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {e : Expr} {t : Lower.Ty} (c : Nat)
      {h h' : Heap F} {r : SourceValue F},
      ExprNoPrefixGe c e →
      HasTy sigs enums Γ e t →
      EvalExpr world [] locals (qualifyExprF F ((inlineCallsM imap e).run c).1) h r h' →
      EvalExpr world [] locals (qualifyExprF F e) h r h'
  | _, _, _, _, _, _, _, _, _, .literal, ev => ev
  | _, _, _, _, _, _, _, _, _, .var _, ev => ev
  | _, _, _, _, c, _, _, _, hnp, .tuple items, ev => by
    rw [inlineCallsM_run_tuple] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple evs =>
      exact .tuple (evalArgs_inlineCallsListM_backward hvalid c hnp items evs)
  | _, _, _, _, c, _, _, _, hnp, .array _ items, ev => by
    rw [inlineCallsM_run_array] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array evs =>
      exact .array (evalArgs_inlineCallsListM_backward hvalid c hnp items evs)
  | _, _, _, _, c, _, _, _, hnp, .repeat hx, ev => by
    rw [inlineCallsM_run_repeat] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item =>
      exact .repeat (evalExpr_inlineCallsM_backward hvalid c hnp hx item)
  | _, _, _, _, c, _, _, _, hnp, .index hx, ev => by
    rw [inlineCallsM_run_index] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp =>
      exact .index (evalExpr_inlineCallsM_backward hvalid c hnp hx item) hp
  | _, _, _, _, c, _, _, _, hnp, .project hx _, ev => by
    rw [inlineCallsM_run_project] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp =>
      exact .project (evalExpr_inlineCallsM_backward hvalid c hnp hx item) hp
  | _, _, _, _, c, _, _, _, hnp, .slice _ hx, ev => by
    rw [inlineCallsM_run_slice] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs =>
      exact .slice (evalExpr_inlineCallsM_backward hvalid c hnp hx item) hs
  | _, _, _, _, c, _, _, _, hnp, .construct _ _ _ _ _ items, ev => by
    rw [inlineCallsM_run_construct] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct evs =>
      exact .construct (evalArgs_inlineCallsListM_backward hvalid c hnp items evs)
  | _, _, _, _, c, _, _, _, hnp, .builtin items, ev => by
    rw [inlineCallsM_run_builtin] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin evs ha =>
      exact .builtin (evalArgs_inlineCallsListM_backward hvalid c hnp items evs) ha
  | _, _, _, _, c, _, _, _, hnp, .store hx, ev => by
    rw [inlineCallsM_run_store] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item =>
      exact .store (evalExpr_inlineCallsM_backward hvalid c hnp hx item)
  | _, _, _, _, c, _, _, _, hnp, .load hx, ev => by
    rw [inlineCallsM_run_load] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl =>
      exact .load (evalExpr_inlineCallsM_backward hvalid c hnp hx item) hl
  | _, _, .hint _ x _, _, c, _, _, _, hnp, .hint _ hx, ev => by
    rw [inlineCallsM_run_hint] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht =>
      exact .hint (evalExpr_inlineCallsM_backward hvalid c (e := x) hnp hx item) ht
  | _, _, _, _, c, _, _, _, hnp, .neg hx, ev => by
    rw [inlineCallsM_run_neg] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop =>
      exact .neg (evalExpr_inlineCallsM_backward hvalid c hnp hx item) hop
  | _, _, .binary _ l r, _, c, _, _, _, hnp, .binary hl hr, ev => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl l c).1
    have hnpL : ExprNoPrefixGe c l :=
      ⟨fun v hv => hnp.1 v (by simp [hasFreeVar, hv]), fun v hv => hnp.2 v (by simp [hasBoundVar, hv])⟩
    have hnpR : ExprNoPrefixGe ((inlineCallsM imap l).run c).2 r :=
      (ExprNoPrefixGe.mono hle
        ⟨fun v hv => hnp.1 v (by simp [hasFreeVar, hv]), fun v hv => hnp.2 v (by simp [hasBoundVar, hv])⟩)
    rw [inlineCallsM_run_binary] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | binary evL evR hop =>
      exact .binary
        (evalExpr_inlineCallsM_backward hvalid c hnpL hl evL)
        (evalExpr_inlineCallsM_backward hvalid _ hnpR hr evR) hop
  | _, _, .letValue _ v _, _, c, _, _, _, hnp, .letValue hx _ hb, ev => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl v c).1
    rw [inlineCallsM_run_letValue] at ev
    rw [qualifyExprF_letValue] at ev ⊢
    cases ev with | letValue evX hm evB =>
      exact .letValue
        (evalExpr_inlineCallsM_backward hvalid c (exprNoPrefixGe_letValue_rhs hnp) hx evX)
        hm
        (evalExpr_inlineCallsM_backward hvalid _ ((exprNoPrefixGe_letValue_body hnp).mono hle) hb evB)
  | _, _, .matchValue s _, _, c, _, _, _, hnp, .matchValue hs harms, ev => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl s c).1
    rw [inlineCallsM_run_matchValue] at ev
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | matchValue evS hsel evB =>
      have evSOrig := evalExpr_inlineCallsM_backward hvalid c (exprNoPrefixGe_matchValue_scrut hnp) hs evS
      rw [map_qualifyArmsF] at hsel
      obtain ⟨p, b, cb, hmem, hleCb, rfl, _, hselOrig⟩ :=
        selectArm_inlineCallsArmsM (c := ((inlineCallsM imap s).run c).2) hsel
      obtain ⟨_, _, hb⟩ := harms.mem hmem
      have hnpB := (armsNoPrefixGe_mem (armsNoPrefixGe_matchValue hnp) hmem).mono (Nat.le_trans hle hleCb)
      rw [← map_qualifyArmsF] at hselOrig
      exact .matchValue evSOrig hselOrig (evalExpr_inlineCallsM_backward hvalid cb hnpB hb evB)
  | Γ, locals, .call nm (some []) xs, t, c, h, h', r, hnp, .call hsig items, ev => by
    have hcl := inlineMapValid_closed hvalid
    have hxsV := inlineCallsListM_vars hcl xs c
    have hxsTy := hasTyList_inlineCallsListM hvalid c hnp items
    rcases inlineCallsM_run_call_cases imap nm (some []) xs c with hno | ⟨callee, _, hl, hlen, hres⟩
    · rw [hno] at ev
      rw [qualifyExprF_call] at ev ⊢
      cases ev with | call evs hfn =>
        exact .call (evalArgs_inlineCallsListM_backward hvalid c hnp items evs) hfn
    · rw [hres] at ev
      obtain ⟨_, _, _, hnoCol, hdist, _, hprovCal, htyCal, _, _, _⟩ := hvalid.mem nm callee hl
      let c1 := ((inlineCallsListM imap xs).run c).2
      let xs' := ((inlineCallsListM imap xs).run c).1
      let pNames := callee.params.map Prod.fst
      have hlen' : pNames.length = xs'.length := by simp [pNames, xs', hlen]
      have hnf : ∀ p ∈ pNames, hasFreeVarList (inlinePfx c1 ++ p) xs' = false := by
        intro p _
        cases hf : hasFreeVarList (inlinePfx c1 ++ p) xs' with
        | false => rfl
        | true =>
          exact absurd rfl (ne_inlinePfx_of_noPrefixGe (hnp.1 _ (hxsV.2.1 _ hf)) hxsV.1 p)
      obtain ⟨vs, hm, hlenVs, evArgs', evBodyPref⟩ :=
        evalExpr_bindParams_inv (inlinePfx c1) pNames xs'
          (prefixExpr (inlinePfx c1) pNames callee.body) hlen' hxsTy.isClean hnf ev
      have evArgsOrig := evalArgs_inlineCallsListM_backward hvalid c hnp items evArgs'
      have hnd : pNames.Nodup := nodup_of_allDistinct hdist
      have hndPref : ((pNames.map (inlinePfx c1 ++ ·)).zip vs |>.map Prod.fst).Nodup := by
        have hmapEq : ((pNames.map (inlinePfx c1 ++ ·)).zip vs).map Prod.fst = pNames.map (inlinePfx c1 ++ ·) :=
          List.map_fst_zip (by simp [hlen', hlenVs])
        rw [hmapEq]
        exact hnd.map fun _ _ heq => string_append_left_inj heq
      have evBodyOrig : EvalExpr world [] (pNames.zip vs) (qualifyExprF F callee.body) hm r h' := by
        refine evalExpr_prefixExpr_backward (inlinePfx c1) pNames htyCal.isClean (fun x hfx => ?_) evBodyPref
        have hxMem : x ∈ pNames := hasFreeVar_of_hasTy htyCal x hfx
        refine ⟨hxMem, ?_⟩
        have hmemRev : inlinePfx c1 ++ x ∈
            (((pNames.map (inlinePfx c1 ++ ·)).zip vs).reverse).map Prod.fst := by
          rw [List.map_reverse]
          refine List.mem_reverse.mpr ?_
          rw [List.map_fst_zip (by simp [hlen', hlenVs])]
          exact List.mem_map.mpr ⟨x, hxMem, rfl⟩
        have hfindApp : ((((pNames.map (inlinePfx c1 ++ ·)).zip vs).reverse ++ locals).find?
            (·.1 == inlinePfx c1 ++ x)) =
            (((pNames.map (inlinePfx c1 ++ ·)).zip vs).reverse).find? (·.1 == inlinePfx c1 ++ x) :=
          find?_append_of_mem_poly hmemRev
        rw [hfindApp, find?_reverse_of_nodup hndPref]
        have hzipMap : (pNames.map (inlinePfx c1 ++ ·)).zip vs =
            (pNames.zip vs).map (fun q => (inlinePfx c1 ++ q.1, q.2)) := by
          clear hmemRev hfindApp hndPref hnd hlen' hlenVs evArgs' evBodyPref evArgsOrig
          induction pNames generalizing vs with
          | nil => cases vs <;> rfl
          | cons p ps ih =>
            cases vs with
            | nil => rfl
            | cons v vs' => simp [ih]
        rw [hzipMap]
        have hfindPref : ∀ (l : List (String × SourceValue F)),
            ((l.map fun q => (inlinePfx c1 ++ q.1, q.2)).find? (·.1 == inlinePfx c1 ++ x)).map Prod.snd =
            (l.find? (·.1 == x)).map Prod.snd := by
          intro l; induction l with
          | nil => rfl
          | cons hd tl ih =>
            rcases hd with ⟨k, v⟩
            simp only [List.map_cons, List.find?_cons]
            by_cases hkx : k = x
            · subst hkx; simp
            · have hne : inlinePfx c1 ++ k ≠ inlinePfx c1 ++ x := fun heq => hkx (string_append_left_inj heq)
              simp only [beq_false_of_ne hkx, beq_false_of_ne hne]; exact ih
        exact (hfindPref (pNames.zip vs)).symm
      have hq : qualifyName nm = qualified nm := by simp [qualifyName, hnoCol]
      rw [qualifyExprF_call]
      refine .call evArgsOrig ?_
      rw [hq]
      have hfn : EvalFn world (qualified nm) vs hm r h' :=
        .intro (hprovCal vs (by rw [hlenVs, ← hlen'])) evBodyOrig
      simpa [instanceName, Instance.symbol] using hfn
termination_by _ _ e _ _ _ _ _ _ _ _ => sizeOf e
decreasing_by
  all_goals try simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp only [Prod.mk.sizeOf_spec] at this; omega)

theorem evalArgs_inlineCallsListM_backward {world : World F} {sigs : FnSigs}
    {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)}
    (hvalid : InlineMapValid world sigs enums imap) :
    ∀ {Γ : TyEnv} {locals : Environment F Nat} {xs : List Expr} {ts : List Lower.Ty} (c : Nat)
      {h h' : Heap F} {vs : List (SourceValue F)},
      ListNoPrefixGe c xs →
      HasTyList sigs enums Γ xs ts →
      EvalArgs world [] locals (((inlineCallsListM imap xs).run c).1.map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h'
  | _, _, _, _, _, _, _, _, _, .nil, ev => by cases ev; exact .nil
  | _, _, x :: xs, _, c, _, _, _, hnp, .cons hd tl, ev => by
    have hcl := inlineMapValid_closed hvalid
    have hle := (inlineCallsM_vars hcl x c).1
    have hnpH : ExprNoPrefixGe c x :=
      ⟨fun v hv => hnp.1 v (by simp [hasFreeVarList, hv]), fun v hv => hnp.2 v (by simp [hasBoundVarList, hv])⟩
    have hnpT : ListNoPrefixGe ((inlineCallsM imap x).run c).2 xs :=
      (ListNoPrefixGe.mono hle
        ⟨fun v hv => hnp.1 v (by simp [hasFreeVarList, hv]), fun v hv => hnp.2 v (by simp [hasBoundVarList, hv])⟩)
    rw [inlineCallsListM_run_cons] at ev
    simp only [List.map_cons] at ev ⊢
    cases ev with | cons evH evT =>
      exact .cons (evalExpr_inlineCallsM_backward hvalid c hnpH hd evH)
        (evalArgs_inlineCallsListM_backward hvalid _ hnpT tl evT)
termination_by _ _ xs _ _ _ _ _ _ _ _ => sizeOf xs

end

end InlineCallsEval

end InlineCallsProof

/-! ## Section 8: Stage 6 (`simpExpr`: Copy Prop, Ctor Folding, Dead-Let & Compact Round-Trip) Backward Soundness -/

section SimpExprProof

/-! ### Part 8A: Structural Characterization Lemmas for `simpExpr`, `shadowMaps`, `pickCtorArm` -/

theorem mem_of_lookup_eq_some {α : Type} :
    ∀ {l : List (String × α)} {k : String} {v : α}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (k0, v0) :: tl, k, v, h => by
    simp only [List.lookup] at h
    by_cases hk : k = k0
    · subst hk; simp only [beq_self_eq_true, Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · simp only [beq_false_of_ne hk] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

theorem lookup_filter_key_eq {α : Type} (bs : List String) :
    ∀ (l : List (String × α)) (x : String),
      x ∉ bs → (l.filter fun q => !bs.contains q.1).lookup x = l.lookup x
  | [], _, _ => rfl
  | (k, v) :: tl, x, hnot => by
    simp only [List.filter_cons]
    by_cases hk : k ∈ bs
    · have hne : x ≠ k := fun heq => hnot (heq ▸ hk)
      have hc : (!bs.contains k) = false := by simp [hk]
      simp only [hc, Bool.false_eq_true, ↓reduceIte, List.lookup, beq_false_of_ne hne]
      exact lookup_filter_key_eq bs tl x hnot
    · have hc : (!bs.contains k) = true := by simp [hk]
      simp only [hc, ↓reduceIte, List.lookup]
      by_cases hxk : x = k
      · subst hxk; simp
      · simp only [beq_false_of_ne hxk]
        exact lookup_filter_key_eq bs tl x hnot

theorem lookup_filter_key_none {α : Type} (bs : List String) :
    ∀ (l : List (String × α)) (x : String),
      x ∈ bs → (l.filter fun q => !bs.contains q.1).lookup x = none
  | [], _, _ => rfl
  | (k, v) :: tl, x, hmem => by
    simp only [List.filter_cons]
    by_cases hk : k ∈ bs
    · have hc : (!bs.contains k) = false := by simp [hk]
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact lookup_filter_key_none bs tl x hmem
    · have hc : (!bs.contains k) = true := by simp [hk]
      have hne : x ≠ k := fun heq => hk (heq ▸ hmem)
      simp only [hc, ↓reduceIte, List.lookup, beq_false_of_ne hne]
      exact lookup_filter_key_none bs tl x hmem

theorem shadowMaps_aliases_eq (bs : List String) (aliases : AliasMap)
    (ctors : CtorMap) (compacts : AliasMap)
    (hno2 : ∀ q ∈ aliases, q.2 ∉ bs) :
    (shadowMaps bs aliases ctors compacts).1 = aliases.filter (fun q => !bs.contains q.1) := by
  simp only [shadowMaps]
  induction aliases with
  | nil => rfl
  | cons q tl ih =>
    have hq2 : (!bs.contains q.2) = true := by simp [hno2 q List.mem_cons_self]
    simp only [List.filter_cons, hq2, Bool.and_true]
    rw [ih (fun r hr => hno2 r (List.mem_cons_of_mem _ hr))]

theorem resolveAlias_shadowMaps (bs : List String) (aliases : AliasMap)
    (ctors : CtorMap) (compacts : AliasMap)
    (hno2 : ∀ q ∈ aliases, q.2 ∉ bs) (x : String) :
    resolveAlias (shadowMaps bs aliases ctors compacts).1 x =
      if x ∈ bs then x else resolveAlias aliases x := by
  rw [shadowMaps_aliases_eq bs aliases ctors compacts hno2]
  unfold resolveAlias
  by_cases hx : x ∈ bs
  · rw [lookup_filter_key_none bs aliases x hx]; simp [hx]
  · rw [lookup_filter_key_eq bs aliases x hx]; simp [hx]

theorem resolveAlias_cons_filter (v y : String) (aliases : AliasMap) (x : String) :
    resolveAlias ((v, y) :: aliases.filter (fun q => q.1 != v)) x =
      if x = v then y else resolveAlias aliases x := by
  unfold resolveAlias
  by_cases hx : x = v
  · subst hx; simp [List.lookup]
  · simp only [hx, ↓reduceIte, List.lookup, beq_false_of_ne hx]
    have hfilt : (aliases.filter fun q => q.1 != v) = aliases.filter (fun q => !([v].contains q.1)) := by
      congr 1; funext q; cases h : (q.1 == v) <;> simp_all [bne, beq_iff_eq]
    rw [hfilt, lookup_filter_key_eq [v] aliases x (by simp [hx])]

theorem resolveAlias_append_filter (binds : AliasMap) (aliases : AliasMap) (x : String) :
    resolveAlias (binds ++ aliases.filter (fun q => !(binds.map Prod.fst).contains q.1)) x =
      match binds.lookup x with
      | some y => y
      | none => resolveAlias aliases x := by
  unfold resolveAlias
  by_cases hx : x ∈ binds.map Prod.fst
  · rw [lookup_append_of_mem_poly hx]
    cases hl : binds.lookup x with
    | some y => rfl
    | none =>
      exfalso
      induction binds with
      | nil => cases hx
      | cons q tl ih =>
        rcases q with ⟨k, v⟩
        simp only [List.map_cons, List.mem_cons] at hx
        simp only [List.lookup] at hl
        by_cases hxk : x = k
        · subst hxk; simp at hl
        · simp only [beq_false_of_ne hxk] at hl
          exact ih (hx.resolve_left hxk) hl
  · rw [lookup_append_of_not_mem_poly hx, lookup_filter_key_eq (binds.map Prod.fst) aliases x hx]
    have hnone : binds.lookup x = none := by
      induction binds with
      | nil => rfl
      | cons q tl ih =>
        rcases q with ⟨k, v⟩
        simp only [List.map_cons, List.mem_cons, not_or] at hx
        simp only [List.lookup, beq_false_of_ne hx.1]
        exact ih hx.2
    rw [hnone]

theorem allVarNames_inv : ∀ {args : List Expr} {fvs : List String},
    allVarNames args = some fvs → args = fvs.map Aiur.Generic.Expr.var
  | [], _, h => by simp [allVarNames] at h; subst h; rfl
  | .var v :: rest, fvs, h => by
    simp only [allVarNames] at h
    cases hr : allVarNames rest with
    | none => rw [hr] at h; cases h
    | some fvs' =>
      rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      exact congrArg (Aiur.Generic.Expr.var v :: ·) (allVarNames_inv hr)
  | .literal _ :: _, _, h | .global _ _ :: _, _, h | .control _ _ :: _, _, h
  | .tuple _ :: _, _, h | .array _ :: _, _, h | .construct _ _ _ _ :: _, _, h
  | .constructAs _ _ _ _ :: _, _, h | .record _ _ :: _, _, h | .update _ _ :: _, _, h
  | .builtin _ _ :: _, _, h | .call _ _ _ :: _, _, h | .repeat _ _ :: _, _, h
  | .index _ _ :: _, _, h | .slice _ _ _ :: _, _, h | .member _ _ :: _, _, h
  | .project _ _ :: _, _, h | .store _ :: _, _, h | .load _ :: _, _, h
  | .hint _ _ _ :: _, _, h | .neg _ :: _, _, h | .binary _ _ _ :: _, _, h
  | .letValue _ _ _ :: _, _, h | .matchValue _ _ :: _, _, h => by simp [allVarNames] at h

theorem matchCompactU32_inv {e inner : Expr} (h : matchCompactU32 e = some inner) :
    e = .call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [inner]] := by
  unfold matchCompactU32 at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · cases h

theorem pickCtorArm_mem {enumTy nm : String} {fvs : List String} :
    ∀ {arms : List (Pat × Expr)} {binds : AliasMap} {armBody : Expr},
      pickCtorArm enumTy nm fvs arms = some (binds, armBody) →
      ∃ p, (p, armBody) ∈ arms ∧
        ((p = .wildcard ∧ binds = []) ∨
         (∃ pats, p = .construct (.named enumTy []) nm pats ∧
           pats.length = fvs.length ∧ matchCtorPats pats fvs = some binds))
  | [], _, _, h => by simp [pickCtorArm] at h
  | (.construct (.named ty' []) nm' pats, body) :: rest, binds, armBody, h => by
    simp only [pickCtorArm] at h
    split at h
    · next hcond =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨rfl, rfl⟩, hlen⟩ := hcond
      cases hm : matchCtorPats pats fvs with
      | none => simp [hm] at h
      | some bs =>
        rw [hm] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, List.mem_cons_self, Or.inr ⟨pats, rfl, hlen, hm⟩⟩
    · obtain ⟨p0, hmem, hcase⟩ := pickCtorArm_mem h
      exact ⟨p0, List.mem_cons_of_mem _ hmem, hcase⟩
  | (.wildcard, body) :: _, binds, armBody, h => by
    simp only [pickCtorArm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.wildcard, List.mem_cons_self, Or.inl ⟨rfl, rfl⟩⟩
  | (.literal _, _) :: rest, _, _, h | (.tuple _, _) :: rest, _, _, h
  | (.array _, _) :: rest, _, _, h | (.repeat _ _, _) :: rest, _, _, h => by
    simp only [pickCtorArm] at h
    obtain ⟨p0, hmem, hcase⟩ := pickCtorArm_mem h
    exact ⟨p0, List.mem_cons_of_mem _ hmem, hcase⟩
  | (.construct (.named _ (_ :: _)) _ _, _) :: _, _, _, h
  | (.construct .field _ _, _) :: _, _, _, h
  | (.construct (.tuple _) _ _, _) :: _, _, _, h | (.construct (.array _ _) _ _, _) :: _, _, _, h
  | (.construct (.ptr _) _ _, _) :: _, _, _, h | (.construct (.param _) _ _, _) :: _, _, _, h
  | (.bind _, _) :: _, _, _, h | (.global _ _, _) :: _, _, _, h | (.load _, _) :: _, _, _, h
  | (.orElse _ _ _, _) :: _, _, _, h | (.record _ _, _) :: _, _, _, h
  | (.constructAs _ _ _ _, _) :: _, _, _, h => by simp [pickCtorArm] at h

theorem matchCtorPats_snd_mem :
    ∀ {pats : List Pat} {fvs : List String} {binds : AliasMap},
      matchCtorPats pats fvs = some binds →
      ∀ q ∈ binds, q.2 ∈ fvs
  | [], [], _, h => by simp [matchCtorPats] at h; subst h; intro _ hm; cases hm
  | .bind v :: ps, fv :: fvs, binds, h => by
    simp only [matchCtorPats] at h
    cases hr : matchCtorPats ps fvs with
    | none => rw [hr] at h; cases h
    | some bs =>
      rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | htl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (matchCtorPats_snd_mem hr q htl)
  | .wildcard :: ps, _ :: fvs, binds, h => by
    simp only [matchCtorPats] at h
    intro q hq
    exact List.mem_cons_of_mem _ (matchCtorPats_snd_mem h q hq)
  | .bind _ :: _, [], _, h | .wildcard :: _, [], _, h | [], _ :: _, _, h
  | .literal _ :: _, _, _, h | .global _ _ :: _, _, _, h | .load _ :: _, _, _, h
  | .orElse _ _ _ :: _, _, _, h | .tuple _ :: _, _, _, h | .array _ :: _, _, _, h
  | .repeat _ _ :: _, _, _, h | .record _ _ :: _, _, _, h | .construct _ _ _ :: _, _, _, h
  | .constructAs _ _ _ _ :: _, _, _, h => by simp [matchCtorPats] at h

theorem simpExprList_length (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) (compacts : AliasMap) :
    ∀ xs : List Expr, (simpExprList fuel aliases ctors compacts xs).length = xs.length
  | [] => by rw [simpExprList]
  | _ :: xs => by rw [simpExprList]; exact congrArg Nat.succ (simpExprList_length fuel aliases ctors compacts xs)

theorem simpExpr_call_cases (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap)
    (compacts : AliasMap) (nm : String) (targs : Option (List Lower.Ty)) (xs : List Expr) :
    let xs' := simpExprList fuel aliases ctors compacts xs
    let res := simpExpr fuel aliases ctors compacts (.call nm targs xs)
    (res = .call nm targs xs') ∨
    ((nm = "u32_of_field" ∨ nm = "UInt32::from_field") ∧ targs = some [] ∧
      ((∃ x0 t u, xs = [x0] ∧ simpExpr fuel aliases ctors compacts x0 = .var t ∧
          compacts.lookup t = some u ∧ res = .var u) ∨
       (∃ x0 arg inner, xs = [x0] ∧ simpExpr fuel aliases ctors compacts x0 = arg ∧
          matchCompactU32 arg = some inner ∧ res = inner))) := by
  dsimp only
  rw [simpExpr]
  split
  · next hcond =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
    obtain ⟨hnm, rfl⟩ := hcond
    cases xs with
    | nil => rw [simpExprList]; exact Or.inl rfl
    | cons x0 rest =>
      cases rest with
      | cons x1 rest2 =>
        rw [simpExprList, simpExprList]
        cases simpExpr fuel aliases ctors compacts x0 <;> exact Or.inl rfl
      | nil =>
        rw [simpExprList, simpExprList]
        cases hx0 : simpExpr fuel aliases ctors compacts x0 with
        | var t =>
          dsimp only
          cases hl : compacts.lookup t with
          | none => exact Or.inl rfl
          | some u => exact Or.inr ⟨hnm, rfl, Or.inl ⟨x0, t, u, rfl, hx0, hl, rfl⟩⟩
        | literal _ | global _ _ | control _ _ | tuple _ | array _ | construct _ _ _ _
        | constructAs _ _ _ _ | record _ _ | update _ _ | builtin _ _ | call _ _ _
        | «repeat» _ _ | index _ _ | slice _ _ _ | member _ _ | project _ _ | store _
        | load _ | hint _ _ _ | neg _ | binary _ _ _ | letValue _ _ _ | matchValue _ _ =>
          dsimp only
          cases hm : matchCompactU32 _ with
          | none => exact Or.inl rfl
          | some inner => exact Or.inr ⟨hnm, rfl, Or.inr ⟨x0, _, inner, rfl, hx0, hm, rfl⟩⟩
  · exact Or.inl rfl

theorem simpExpr_letValue_nonBind (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap)
    (compacts : AliasMap) (p : Pat) (x b : Expr) (hnb : ∀ v, p ≠ .bind v) :
    simpExpr fuel aliases ctors compacts (.letValue p x b) =
      let (a0, c0, m0) := shadowMaps (patBoundVars p) aliases ctors compacts
      .letValue p (simpExpr fuel aliases ctors compacts x) (simpExpr fuel a0 c0 m0 b) := by
  cases p with
  | bind v => exact absurd rfl (hnb v)
  | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
  | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
    rw [simpExpr]

private theorem simpLetPost_var_cases (v : String) (x' b' : Expr) (hp : isPureCtorOrVar x' = true) :
    let res := match b' with
      | .var w => if w == v then x' else .letValue (.bind v) x' b'
      | _ => if !hasFreeVar v b' then b' else .letValue (.bind v) x' b'
    res = .letValue (.bind v) x' b' ∨ (res = x' ∧ b' = .var v) ∨
      (res = b' ∧ isPureCtorOrVar x' = true ∧ hasFreeVar v b' = false) := by
  cases b' with
  | var w =>
    dsimp only
    by_cases hwv : w = v
    · subst hwv; exact Or.inr (Or.inl ⟨by simp, rfl⟩)
    · exact Or.inl (by simp [beq_false_of_ne hwv])
  | literal _ | global _ _ | control _ _ | tuple _ | array _ | construct _ _ _ _
  | constructAs _ _ _ _ | record _ _ | update _ _ | builtin _ _ | call _ _ _
  | «repeat» _ _ | index _ _ | slice _ _ _ | member _ _ | project _ _ | store _
  | load _ | hint _ _ _ | neg _ | binary _ _ _ | letValue _ _ _ | matchValue _ _ =>
    dsimp only
    cases hfv : hasFreeVar v _ with
    | false => exact Or.inr (Or.inr ⟨by simp, hp, rfl⟩)
    | true => exact Or.inl (by simp)

private theorem simpLetPost_ctor_cases (v : String) (x' b' : Expr) :
    let res := if isPureCtorOrVar x' && !hasFreeVar v b' then b'
      else match b' with
        | .var w => if w == v then x' else .letValue (.bind v) x' b'
        | _ => .letValue (.bind v) x' b'
    res = .letValue (.bind v) x' b' ∨ (res = x' ∧ b' = .var v) ∨
      (res = b' ∧ isPureCtorOrVar x' = true ∧ hasFreeVar v b' = false) := by
  dsimp only
  cases hp : isPureCtorOrVar x' with
  | true =>
    cases hfv : hasFreeVar v b' with
    | false => exact Or.inr (Or.inr ⟨by simp, rfl, rfl⟩)
    | true =>
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      cases b' with
      | var w =>
        dsimp only
        by_cases hwv : w = v
        · subst hwv; exact Or.inr (Or.inl ⟨by simp, rfl⟩)
        · exact Or.inl (by simp [beq_false_of_ne hwv])
      | _ => exact Or.inl rfl
  | false =>
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    cases b' with
    | var w =>
      dsimp only
      by_cases hwv : w = v
      · subst hwv; exact Or.inr (Or.inl ⟨by simp, rfl⟩)
      · exact Or.inl (by simp [beq_false_of_ne hwv])
    | _ => exact Or.inl rfl

private theorem simpLetPost_other_cases (v : String) (x' b' : Expr) :
    let res := match b' with
      | .var w => if w == v then x' else .letValue (.bind v) x' b'
      | _ => if isPureCtorOrVar x' && !hasFreeVar v b' then b' else .letValue (.bind v) x' b'
    res = .letValue (.bind v) x' b' ∨ (res = x' ∧ b' = .var v) ∨
      (res = b' ∧ isPureCtorOrVar x' = true ∧ hasFreeVar v b' = false) := by
  cases b' with
  | var w =>
    dsimp only
    by_cases hwv : w = v
    · subst hwv; exact Or.inr (Or.inl ⟨by simp, rfl⟩)
    · exact Or.inl (by simp [beq_false_of_ne hwv])
  | literal _ | global _ _ | control _ _ | tuple _ | array _ | construct _ _ _ _
  | constructAs _ _ _ _ | record _ _ | update _ _ | builtin _ _ | call _ _ _
  | «repeat» _ _ | index _ _ | slice _ _ _ | member _ _ | project _ _ | store _
  | load _ | hint _ _ _ | neg _ | binary _ _ _ | letValue _ _ _ | matchValue _ _ =>
    dsimp only
    cases hp : isPureCtorOrVar x' with
    | true =>
      cases hfv : hasFreeVar v _ with
      | false => exact Or.inr (Or.inr ⟨by simp, rfl, rfl⟩)
      | true => exact Or.inl (by simp)
    | false => exact Or.inl (by simp)

/-- Unified characterization of `simpExpr` on `.letValue (.bind v) x b`. -/
theorem simpExpr_letValue_bind_cases (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap)
    (compacts : AliasMap) (v : String) (x b : Expr) :
    let x' := simpExpr fuel aliases ctors compacts x
    let (a0, c0, m0) := shadowMaps [v] aliases ctors compacts
    let res := simpExpr fuel aliases ctors compacts (.letValue (.bind v) x b)
    (∃ y, x' = .var y ∧ hasBoundVar y b = false ∧
      res = simpExpr fuel ((v, y) :: aliases.filter (fun q => q.1 != v)) ctors compacts b) ∨
    (∃ ctors1 compacts1,
      (ctors1 = c0 ∨ ∃ ty nm args fvs, x' = .construct ty (some []) nm args ∧
        allVarNames args = some fvs ∧ v ∉ fvs ∧ ctors1 = (v, (ty, nm, fvs)) :: c0) ∧
      (compacts1 = m0 ∨ ∃ u, matchCompactU32 x' = some (.var u) ∧ u ≠ v ∧ compacts1 = (v, u) :: m0) ∧
      let b' := simpExpr fuel a0 ctors1 compacts1 b
      (res = .letValue (.bind v) x' b' ∨
       (res = x' ∧ b' = .var v) ∨
       (res = b' ∧ isPureCtorOrVar x' = true ∧ hasFreeVar v b' = false))) := by
  dsimp only
  rw [simpExpr]
  simp only [patBoundVars]
  cases hx' : simpExpr fuel aliases ctors compacts x with
  | var y =>
    dsimp only
    cases hbv : hasBoundVar y b with
    | false =>
      exact Or.inl ⟨y, rfl, hbv, by simp⟩
    | true =>
      refine Or.inr ⟨(shadowMaps [v] aliases ctors compacts).2.1,
        (shadowMaps [v] aliases ctors compacts).2.2, Or.inl rfl, Or.inl rfl, ?_⟩
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact simpLetPost_var_cases v (.var y) _ rfl
  | construct ty targs nm args =>
    dsimp only
    let ctors1 := match targs, allVarNames args with
      | some [], some fvs =>
        if !fvs.contains v then (v, (ty, nm, fvs)) :: (shadowMaps [v] aliases ctors compacts).2.1
        else (shadowMaps [v] aliases ctors compacts).2.1
      | _, _ => (shadowMaps [v] aliases ctors compacts).2.1
    refine Or.inr ⟨ctors1, (shadowMaps [v] aliases ctors compacts).2.2, ?_, Or.inl rfl, ?_⟩
    · dsimp only [ctors1]
      cases targs with
      | none => exact Or.inl rfl
      | some ts =>
        cases ts with
        | cons _ _ => exact Or.inl rfl
        | nil =>
          cases hav : allVarNames args with
          | none => exact Or.inl rfl
          | some fvs =>
            dsimp only
            by_cases hmem : v ∈ fvs
            · simp [hmem]
            · refine Or.inr ⟨ty, nm, args, fvs, rfl, hav, hmem, ?_⟩; simp [hmem]
    · exact simpLetPost_ctor_cases v (.construct ty targs nm args) _
  | literal _ | global _ _ | control _ _ | tuple _ | array _ | constructAs _ _ _ _
  | record _ _ | update _ _ | builtin _ _ | call _ _ _ | «repeat» _ _ | index _ _
  | slice _ _ _ | member _ _ | project _ _ | store _ | load _ | hint _ _ _ | neg _
  | binary _ _ _ | letValue _ _ _ | matchValue _ _ =>
    dsimp only
    rw [← hx']
    let x' := simpExpr fuel aliases ctors compacts x
    let compacts1 := match matchCompactU32 x' with
      | some (.var u) =>
        if u != v then (v, u) :: (shadowMaps [v] aliases ctors compacts).2.2
        else (shadowMaps [v] aliases ctors compacts).2.2
      | _ => (shadowMaps [v] aliases ctors compacts).2.2
    refine Or.inr ⟨(shadowMaps [v] aliases ctors compacts).2.1, compacts1, Or.inl rfl, ?_, ?_⟩
    · dsimp only [compacts1]
      cases hm : matchCompactU32 x' with
      | none => exact Or.inl rfl
      | some inner =>
        cases inner with
        | var u =>
          dsimp only
          by_cases huv : u = v
          · subst huv; simp
          · refine Or.inr ⟨u, rfl, huv, ?_⟩; simp [bne_iff_ne, huv]
        | _ => exact Or.inl rfl
    · exact simpLetPost_other_cases v x' _

/-- Unified characterization of `simpExpr` on `.matchValue scrut arms`. -/
theorem simpExpr_matchValue_cases (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap)
    (compacts : AliasMap) (scrut : Expr) (arms : List (Pat × Expr)) :
    let scrut' := simpExpr fuel aliases ctors compacts scrut
    let res := simpExpr fuel aliases ctors compacts (.matchValue scrut arms)
    (res = .matchValue scrut' (simpArms fuel aliases ctors compacts arms)) ∨
    (∃ fuel' enumTy nm fvs binds armBody,
      fuel = fuel' + 1 ∧
      ((∃ v, scrut' = .var v ∧ ctors.lookup v = some (enumTy, nm, fvs)) ∨
       (∃ args, scrut' = .construct enumTy (some []) nm args ∧ allVarNames args = some fvs)) ∧
      pickCtorArm enumTy nm fvs arms = some (binds, armBody) ∧
      Lower.allDistinct (binds.map Prod.fst) = true ∧
      (∀ q ∈ binds, hasBoundVar q.2 armBody = false) ∧
      res = simpExpr fuel' (binds ++ aliases.filter (fun q => !(binds.map Prod.fst).contains q.1))
        ctors compacts armBody) := by
  dsimp only
  cases fuel with
  | zero => rw [simpExpr]; exact Or.inl rfl
  | succ fuel' =>
    rw [simpExpr]
    dsimp only
    generalize hsc : simpExpr (fuel' + 1) aliases ctors compacts scrut = scrut'
    split
    · next enumTy nm fvs hkn =>
      have hsrc : (∃ v, scrut' = .var v ∧ ctors.lookup v = some (enumTy, nm, fvs)) ∨
          (∃ args, scrut' = .construct enumTy (some []) nm args ∧ allVarNames args = some fvs) := by
        cases scrut' with
        | var v => exact Or.inl ⟨v, rfl, hkn⟩
        | construct ty targs nm' args =>
          cases targs with
          | none => cases hkn
          | some ts =>
            cases ts with
            | cons _ _ => cases hkn
            | nil =>
              cases hav : allVarNames args with
              | none => simp [hav] at hkn
              | some fvs0 =>
                simp only [hav, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkn
                obtain ⟨rfl, rfl, rfl⟩ := hkn
                exact Or.inr ⟨args, rfl, hav⟩
        | _ => cases hkn
      cases hp : pickCtorArm enumTy nm fvs arms with
      | none => exact Or.inl rfl
      | some pb =>
        rcases pb with ⟨binds, armBody⟩
        dsimp only
        cases hcond : (Lower.allDistinct (binds.map Prod.fst) &&
            binds.all fun q => !hasBoundVar q.2 armBody) with
        | false => exact Or.inl rfl
        | true =>
          simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hcond
          exact Or.inr ⟨fuel', enumTy, nm, fvs, binds, armBody, rfl, hsrc, hp, hcond.1, hcond.2, rfl⟩
    · exact Or.inl rfl

/-! ### Part 8B: Syntactic Preservation under `simpExpr` (`hasBoundVar`, `NoLetShadow`, `ExprNoPrefixGe`, `allLitsLt`, `noInlinableCalls`, `literalsBounded`, `noInlinableInBoundedCalls`) -/

private theorem hasBoundVarArms_of_mem {v : String} {p : Pat} {b : Expr} {arms : List (Pat × Expr)}
    (hmem : (p, b) ∈ arms) (hb : hasBoundVar v b = true) : hasBoundVarArms v arms = true := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    simp only [hasBoundVarArms, Bool.or_eq_true]
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact Or.inl (Or.inr hb)
    · exact Or.inr (ih htl)

mutual

/-- `simpExpr` never introduces any new bound variables! -/
theorem hasBoundVar_simpExpr_sub (v : String) :
    ∀ (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) (compacts : AliasMap) (e : Expr),
      hasBoundVar v (simpExpr fuel aliases ctors compacts e) = true → hasBoundVar v e = true
  | _, _, _, _, .literal _, h | _, _, _, _, .var _, h | _, _, _, _, .global _ _, h
  | _, _, _, _, .control _ _, h => by simp [simpExpr, hasBoundVar] at h
  | fuel, a, c, m, .tuple xs, h | fuel, a, c, m, .array xs, h
  | fuel, a, c, m, .construct _ _ _ xs, h | fuel, a, c, m, .constructAs _ _ _ xs, h
  | fuel, a, c, m, .record _ xs, h | fuel, a, c, m, .update _ xs, h
  | fuel, a, c, m, .builtin _ xs, h => by
    rw [simpExpr] at h; exact hasBoundVarList_simpExpr_sub v fuel a c m xs h
  | fuel, a, c, m, .repeat x _, h | fuel, a, c, m, .index x _, h | fuel, a, c, m, .slice x _ _, h
  | fuel, a, c, m, .member x _, h | fuel, a, c, m, .project x _, h | fuel, a, c, m, .store x, h
  | fuel, a, c, m, .load x, h | fuel, a, c, m, .hint _ x _, h | fuel, a, c, m, .neg x, h => by
    rw [simpExpr] at h; exact hasBoundVar_simpExpr_sub v fuel a c m x h
  | fuel, a, c, m, .binary _ l r, h => by
    simp only [simpExpr, hasBoundVar, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_simpExpr_sub v fuel a c m l h1)
    · exact Or.inr (hasBoundVar_simpExpr_sub v fuel a c m r h2)
  | fuel, a, c, m, .call nm targs xs, h => by
    rcases simpExpr_call_cases fuel a c m nm targs xs with hres | ⟨_, _, ⟨x0, t, u, _, _, _, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres] at h; exact hasBoundVarList_simpExpr_sub v fuel a c m xs h
    · rw [hres] at h; simp [hasBoundVar] at h
    · rw [hres] at h
      have harg : hasBoundVar v (simpExpr fuel a c m x0) = true := by
        rw [hx0, matchCompactU32_inv hmc]; simp [hasBoundVar, hasBoundVarList, h]
      simpa [hasBoundVar, hasBoundVarList] using hasBoundVar_simpExpr_sub v fuel a c m x0 harg
  | fuel, a, c, m, .letValue p x b, h => by
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨y, _, _, hres⟩ | ⟨c1, m1, _, _, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres] at h
        exact by simp [hasBoundVar, hasBoundVar_simpExpr_sub v fuel _ c m b h]
      · rw [hres] at h
        simp only [hasBoundVar, Bool.or_eq_true] at h ⊢
        rcases h with (h0 | h1) | h2
        · exact Or.inl (Or.inl h0)
        · exact Or.inl (Or.inr (hasBoundVar_simpExpr_sub v fuel a c m x h1))
        · exact Or.inr (hasBoundVar_simpExpr_sub v fuel _ c1 m1 b h2)
      · rw [hres] at h
        exact by simp [hasBoundVar, hasBoundVar_simpExpr_sub v fuel a c m x h]
      · rw [hres] at h
        exact by simp [hasBoundVar, hasBoundVar_simpExpr_sub v fuel _ c1 m1 b h]
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)] at h
      simp only [hasBoundVar, Bool.or_eq_true] at h ⊢
      rcases h with (h0 | h1) | h2
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr (hasBoundVar_simpExpr_sub v fuel a c m x h1))
      · exact Or.inr (hasBoundVar_simpExpr_sub v fuel _ _ _ b h2)
  | fuel, a, c, m, .matchValue s arms, h => by
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', enumTy, nm, fvs, binds, armBody, rfl, _, hpick, _, _, hres⟩
    · rw [hres] at h
      simp only [hasBoundVar, Bool.or_eq_true] at h ⊢
      rcases h with h1 | h2
      · exact Or.inl (hasBoundVar_simpExpr_sub v fuel a c m s h1)
      · exact Or.inr (hasBoundVarArms_simpExpr_sub v fuel a c m arms h2)
    · rw [hres] at h
      obtain ⟨p, hmem, _⟩ := pickCtorArm_mem hpick
      have hb := hasBoundVar_simpExpr_sub v fuel' _ c m armBody h
      exact by simp [hasBoundVar, hasBoundVarArms_of_mem hmem hb]
termination_by fuel _ _ _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem hasBoundVarList_simpExpr_sub (v : String) :
    ∀ (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) (compacts : AliasMap) (xs : List Expr),
      hasBoundVarList v (simpExprList fuel aliases ctors compacts xs) = true → hasBoundVarList v xs = true
  | _, _, _, _, [], h => by simp [simpExprList, hasBoundVarList] at h
  | fuel, a, c, m, x :: xs, h => by
    simp only [simpExprList, hasBoundVarList, Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (hasBoundVar_simpExpr_sub v fuel a c m x h1)
    · exact Or.inr (hasBoundVarList_simpExpr_sub v fuel a c m xs h2)
termination_by fuel _ _ _ xs _ => (fuel, sizeOf xs)

theorem hasBoundVarArms_simpExpr_sub (v : String) :
    ∀ (fuel : Nat) (aliases : AliasMap) (ctors : CtorMap) (compacts : AliasMap) (arms : List (Pat × Expr)),
      hasBoundVarArms v (simpArms fuel aliases ctors compacts arms) = true → hasBoundVarArms v arms = true
  | _, _, _, _, [], h => by simp [simpArms, hasBoundVarArms] at h
  | fuel, a, c, m, (p, b) :: rest, h => by
    simp only [simpArms, hasBoundVarArms, Bool.or_eq_true] at h ⊢
    rcases h with (h0 | h1) | h2
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr (hasBoundVar_simpExpr_sub v fuel _ _ _ b h1))
    · exact Or.inr (hasBoundVarArms_simpExpr_sub v fuel a c m rest h2)
termination_by fuel _ _ _ arms _ => (fuel, sizeOf arms)

end

mutual

/-- `simpExpr` preserves `NoLetShadow` unconditionally! -/
theorem noLetShadow_simpExpr :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {scope : List String} {e : Expr},
      NoLetShadow scope e → NoLetShadow scope (simpExpr fuel a c m e)
  | _, _, _, _, _, .literal _, _ | _, _, _, _, _, .var _, _ | _, _, _, _, _, .global _ _, _
  | _, _, _, _, _, .control _ _, _ => by rw [simpExpr]; trivial
  | fuel, a, c, m, _, .tuple xs, h | fuel, a, c, m, _, .array xs, h
  | fuel, a, c, m, _, .construct _ _ _ xs, h | fuel, a, c, m, _, .constructAs _ _ _ xs, h
  | fuel, a, c, m, _, .record _ xs, h | fuel, a, c, m, _, .update _ xs, h
  | fuel, a, c, m, _, .builtin _ xs, h => by
    rw [simpExpr]; exact noLetShadowList_simpExprList fuel a c m h
  | fuel, a, c, m, _, .repeat x _, h | fuel, a, c, m, _, .index x _, h | fuel, a, c, m, _, .slice x _ _, h
  | fuel, a, c, m, _, .member x _, h | fuel, a, c, m, _, .project x _, h | fuel, a, c, m, _, .store x, h
  | fuel, a, c, m, _, .load x, h | fuel, a, c, m, _, .hint _ x _, h | fuel, a, c, m, _, .neg x, h => by
    rw [simpExpr]; exact noLetShadow_simpExpr fuel a c m (e := x) h
  | fuel, a, c, m, _, .binary _ l r, ⟨hdisj, hl, hr⟩ => by
    simp only [simpExpr, NoLetShadow]
    refine ⟨fun v hv => ?_, noLetShadow_simpExpr fuel a c m hl, noLetShadow_simpExpr fuel a c m hr⟩
    cases hrb : hasBoundVar v (simpExpr fuel a c m r) with
    | false => rfl
    | true =>
      have := hasBoundVar_simpExpr_sub v fuel a c m r hrb
      rw [hdisj v (hasBoundVar_simpExpr_sub v fuel a c m l hv)] at this; cases this
  | fuel, a, c, m, _, .call nm targs xs, h => by
    rcases simpExpr_call_cases fuel a c m nm targs xs with
      hres | ⟨_, _, ⟨_, _, _, _, _, _, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]; exact noLetShadowList_simpExprList fuel a c m h
    · rw [hres]; trivial
    · rw [hres]
      have hx0' := noLetShadow_simpExpr fuel a c m h.2.1
      rw [hx0, matchCompactU32_inv hmc] at hx0'
      exact hx0'.2.1.2.1
  | fuel, a, c, m, scope, .letValue p x b, ⟨hp, hdisj, hx, hb⟩ => by
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨y, _, _, hres⟩ | ⟨c1, m1, _, _, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres]
        exact noLetShadow_simpExpr fuel _ c m (noLetShadow_scope_imp (fun v hv => Or.inl (List.mem_cons_of_mem _ hv)) hb)
      · rw [hres]
        refine ⟨hp, fun v hv => ?_, noLetShadow_simpExpr fuel a c m hx, noLetShadow_simpExpr fuel _ c1 m1 hb⟩
        obtain ⟨hnp, hnb⟩ := hdisj v (hasBoundVar_simpExpr_sub v fuel a c m x hv)
        refine ⟨hnp, ?_⟩
        cases hbb : hasBoundVar v (simpExpr fuel _ c1 m1 b) with
        | false => rfl
        | true => rw [hasBoundVar_simpExpr_sub v fuel _ c1 m1 b hbb] at hnb; cases hnb
      · rw [hres]; exact noLetShadow_simpExpr fuel a c m hx
      · rw [hres]
        exact noLetShadow_simpExpr fuel _ c1 m1 (noLetShadow_scope_imp (fun v hv => Or.inl (List.mem_cons_of_mem _ hv)) hb)
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      refine ⟨hp, fun v hv => ?_, noLetShadow_simpExpr fuel a c m hx, noLetShadow_simpExpr fuel _ _ _ hb⟩
      obtain ⟨hnp, hnb⟩ := hdisj v (hasBoundVar_simpExpr_sub v fuel a c m x hv)
      refine ⟨hnp, ?_⟩
      cases hbb : hasBoundVar v (simpExpr fuel _ _ _ b) with
      | false => rfl
      | true => rw [hasBoundVar_simpExpr_sub v fuel _ _ _ b hbb] at hnb; cases hnb
  | fuel, a, c, m, scope, .matchValue s arms, ⟨hs, harms⟩ => by
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', enumTy, nm, fvs, binds, armBody, rfl, _, hpick, _, _, hres⟩
    · rw [hres]
      exact ⟨noLetShadow_simpExpr fuel a c m hs, noLetShadowArms_simpArms fuel a c m harms⟩
    · rw [hres]
      obtain ⟨p, hmem, _⟩ := pickCtorArm_mem hpick
      have ⟨_, hnsB⟩ := noLetShadowArms_mem harms hmem
      exact noLetShadow_simpExpr fuel' _ c m
        (noLetShadow_scope_imp (fun v hv => Or.inl (List.mem_append_right _ hv)) hnsB)
termination_by fuel _ _ _ _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem noLetShadowList_simpExprList :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {scope : List String} {xs : List Expr},
      NoLetShadowList scope xs → NoLetShadowList scope (simpExprList fuel a c m xs)
  | _, _, _, _, _, [], _ => by rw [simpExprList]; trivial
  | fuel, a, c, m, _, x :: xs, ⟨hdisj, hx, hxs⟩ => by
    simp only [simpExprList, NoLetShadowList]
    refine ⟨fun v hv => ?_, noLetShadow_simpExpr fuel a c m hx, noLetShadowList_simpExprList fuel a c m hxs⟩
    cases hrb : hasBoundVarList v (simpExprList fuel a c m xs) with
    | false => rfl
    | true =>
      have := hasBoundVarList_simpExpr_sub v fuel a c m xs hrb
      rw [hdisj v (hasBoundVar_simpExpr_sub v fuel a c m x hv)] at this; cases this
termination_by fuel _ _ _ _ xs _ => (fuel, sizeOf xs)

theorem noLetShadowArms_simpArms :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {scope : List String} {arms : List (Pat × Expr)},
      NoLetShadowArms scope arms → NoLetShadowArms scope (simpArms fuel a c m arms)
  | _, _, _, _, _, [], _ => by rw [simpArms]; trivial
  | fuel, a, c, m, _, (p, b) :: rest, ⟨hp, hb, hrest⟩ => by
    simp only [simpArms, NoLetShadowArms]
    exact ⟨hp, noLetShadow_simpExpr fuel _ _ _ hb, noLetShadowArms_simpArms fuel a c m hrest⟩
termination_by fuel _ _ _ _ arms _ => (fuel, sizeOf arms)

end

mutual

/-- `simpExpr` preserves `ExprNoPrefixGe c` when all map targets satisfy `NoPrefixGe c`! -/
theorem exprNoPrefixGe_simpExpr {cnt : Nat} :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {e : Expr},
      (∀ q ∈ a, NoPrefixGe cnt q.2) →
      (∀ q ∈ c, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv) →
      (∀ q ∈ m, NoPrefixGe cnt q.2) →
      ExprNoPrefixGe cnt e →
      ExprNoPrefixGe cnt (simpExpr fuel a c m e)
  | _, _, _, _, .literal _, _, _, _, h | _, _, _, _, .global _ _, _, _, _, h
  | _, _, _, _, .control _ _, _, _, _, h => by rw [simpExpr]; exact h
  | _, a, _, _, .var x, ha, _, _, h => by
    simp only [simpExpr]
    refine ⟨fun v hv => ?_, fun _ hbv => by simp [hasBoundVar] at hbv⟩
    simp only [hasFreeVar, beq_iff_eq] at hv; subst hv
    unfold resolveAlias
    cases hl : a.lookup x with
    | none => exact h.1 x (by simp [hasFreeVar])
    | some y => exact ha (x, y) (mem_of_lookup_eq_some hl)
  | fuel, a, c, m, .tuple xs, ha, hc, hm, h | fuel, a, c, m, .array xs, ha, hc, hm, h
  | fuel, a, c, m, .construct _ _ _ xs, ha, hc, hm, h | fuel, a, c, m, .constructAs _ _ _ xs, ha, hc, hm, h
  | fuel, a, c, m, .record _ xs, ha, hc, hm, h | fuel, a, c, m, .update _ xs, ha, hc, hm, h
  | fuel, a, c, m, .builtin _ xs, ha, hc, hm, h => by
    rw [simpExpr]; exact listNoPrefixGe_simpExprList fuel a c m ha hc hm h
  | fuel, a, c, m, .repeat x _, ha, hc, hm, h | fuel, a, c, m, .index x _, ha, hc, hm, h
  | fuel, a, c, m, .slice x _ _, ha, hc, hm, h | fuel, a, c, m, .member x _, ha, hc, hm, h
  | fuel, a, c, m, .project x _, ha, hc, hm, h | fuel, a, c, m, .store x, ha, hc, hm, h
  | fuel, a, c, m, .load x, ha, hc, hm, h | fuel, a, c, m, .hint _ x _, ha, hc, hm, h
  | fuel, a, c, m, .neg x, ha, hc, hm, h => by
    rw [simpExpr]; exact exprNoPrefixGe_simpExpr fuel a c m ha hc hm (e := x) h
  | fuel, a, c, m, .binary _ l r, ha, hc, hm, h => by
    have hl := exprNoPrefixGe_simpExpr fuel a c m ha hc hm (e := l)
      ⟨fun v hv => h.1 v (by simp [hasFreeVar, hv]), fun v hv => h.2 v (by simp [hasBoundVar, hv])⟩
    have hr := exprNoPrefixGe_simpExpr fuel a c m ha hc hm (e := r)
      ⟨fun v hv => h.1 v (by simp [hasFreeVar, hv]), fun v hv => h.2 v (by simp [hasBoundVar, hv])⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp only [simpExpr, hasFreeVar, Bool.or_eq_true] at hv
      rcases hv with h1 | h2
      · exact hl.1 v h1
      · exact hr.1 v h2
    · simp only [simpExpr, hasBoundVar, Bool.or_eq_true] at hv
      rcases hv with h1 | h2
      · exact hl.2 v h1
      · exact hr.2 v h2
  | fuel, a, c, m, .call nm targs xs, ha, hc, hm, h => by
    rcases simpExpr_call_cases fuel a c m nm targs xs with
      hres | ⟨_, _, ⟨_, t, u, _, _, hl, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]; exact listNoPrefixGe_simpExprList fuel a c m ha hc hm h
    · rw [hres]
      refine ⟨fun v hv => ?_, fun _ hbv => by simp [hasBoundVar] at hbv⟩
      simp only [hasFreeVar, beq_iff_eq] at hv; subst hv
      exact hm (t, u) (mem_of_lookup_eq_some hl)
    · rw [hres]
      have hx0' := exprNoPrefixGe_simpExpr fuel a c m ha hc hm (e := x0)
        ⟨fun v hv => h.1 v (by simp [hasFreeVar, hasFreeVarList, hv]),
         fun v hv => h.2 v (by simp [hasBoundVar, hasBoundVarList, hv])⟩
      rw [hx0, matchCompactU32_inv hmc] at hx0'
      exact ⟨fun v hv => hx0'.1 v (by simp [hasFreeVar, hasFreeVarList, hv]),
             fun v hv => hx0'.2 v (by simp [hasBoundVar, hasBoundVarList, hv])⟩
  | fuel, a, c, m, .letValue p x b, ha, hc, hm, h => by
    have hx' := exprNoPrefixGe_simpExpr fuel a c m ha hc hm (exprNoPrefixGe_letValue_rhs h)
    have hsha : ∀ q ∈ (shadowMaps (patBoundVars p) a c m).1, NoPrefixGe cnt q.2 :=
      fun q hq => ha q (List.mem_filter.mp hq).1
    have hshc : ∀ q ∈ (shadowMaps (patBoundVars p) a c m).2.1, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv :=
      fun q hq => hc q (List.mem_filter.mp hq).1
    have hshm : ∀ q ∈ (shadowMaps (patBoundVars p) a c m).2.2, NoPrefixGe cnt q.2 :=
      fun q hq => hm q (List.mem_filter.mp hq).1
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨y, hy, _, hres⟩ | ⟨c1, m1, hc1, hm1, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres]
        have hyNp : NoPrefixGe cnt y := by
          rw [hy] at hx'; exact hx'.1 y (by simp [hasFreeVar])
        refine exprNoPrefixGe_simpExpr fuel _ c m (fun q hq => ?_) hc hm (exprNoPrefixGe_letValue_body h)
        rcases List.mem_cons.mp hq with rfl | htl
        · exact hyNp
        · exact ha q (List.mem_filter.mp htl).1
      · have hc1' : ∀ q ∈ c1, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv := by
          rcases hc1 with rfl | ⟨ty, nm', args, fvs, hxeq, hav, hnotFvs, rfl⟩
          · exact hshc
          · intro q hq fv hfv
            rcases List.mem_cons.mp hq with rfl | htl
            · rw [hxeq, allVarNames_inv hav] at hx'
              have hfvFree : hasFreeVar fv (.construct ty (some []) nm' (fvs.map Aiur.Generic.Expr.var)) = true := by
                simp only [hasFreeVar]
                have go : ∀ l : List String, fv ∈ l → hasFreeVarList fv (l.map Aiur.Generic.Expr.var) = true := by
                  intro l hl
                  induction l with
                  | nil => cases hl
                  | cons f0 fs ih =>
                    simp only [List.map_cons, hasFreeVarList, hasFreeVar, Bool.or_eq_true, beq_iff_eq]
                    rcases List.mem_cons.mp hl with rfl | htl
                    · exact Or.inl rfl
                    · exact Or.inr (ih htl)
                exact go fvs hfv
              exact hx'.1 fv hfvFree
            · exact hshc q htl fv hfv
        have hm1' : ∀ q ∈ m1, NoPrefixGe cnt q.2 := by
          rcases hm1 with rfl | ⟨u, hmc, _, rfl⟩
          · exact hshm
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | htl
            · rw [matchCompactU32_inv hmc] at hx'
              exact hx'.1 u (by simp [hasFreeVar, hasFreeVarList])
            · exact hshm q htl
        have hb' := exprNoPrefixGe_simpExpr fuel _ c1 m1 hsha hc1' hm1' (exprNoPrefixGe_letValue_body h)
        dsimp only [shadowMaps, patBoundVars] at hb'
        rw [hres]
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · simp only [hasFreeVar, Bool.or_eq_true, Bool.and_eq_true] at hv
          rcases hv with h1 | ⟨_, h2⟩
          · exact hx'.1 v h1
          · exact hb'.1 v h2
        · simp only [hasBoundVar, patBoundVars, List.contains_cons, List.contains_nil, Bool.or_false,
            Bool.or_eq_true, beq_iff_eq] at hv
          rcases hv with (rfl | h1) | h2
          · exact h.2 v (by simp [hasBoundVar, patBoundVars])
          · exact hx'.2 v h1
          · simp only [List.contains_cons, List.contains_nil, Bool.or_false] at hb'
            exact hb'.2 v h2
      · rw [hres]; exact hx'
      · have hc1' : ∀ q ∈ c1, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv := by
          rcases hc1 with rfl | ⟨ty, nm', args, fvs, hxeq, hav, hnotFvs, rfl⟩
          · exact hshc
          · intro q hq fv hfv
            rcases List.mem_cons.mp hq with rfl | htl
            · rw [hxeq, allVarNames_inv hav] at hx'
              have hfvFree : hasFreeVar fv (.construct ty (some []) nm' (fvs.map Aiur.Generic.Expr.var)) = true := by
                simp only [hasFreeVar]
                have go : ∀ l : List String, fv ∈ l → hasFreeVarList fv (l.map Aiur.Generic.Expr.var) = true := by
                  intro l hl
                  induction l with
                  | nil => cases hl
                  | cons f0 fs ih =>
                    simp only [List.map_cons, hasFreeVarList, hasFreeVar, Bool.or_eq_true, beq_iff_eq]
                    rcases List.mem_cons.mp hl with rfl | htl
                    · exact Or.inl rfl
                    · exact Or.inr (ih htl)
                exact go fvs hfv
              exact hx'.1 fv hfvFree
            · exact hshc q htl fv hfv
        have hm1' : ∀ q ∈ m1, NoPrefixGe cnt q.2 := by
          rcases hm1 with rfl | ⟨u, hmc, _, rfl⟩
          · exact hshm
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | htl
            · rw [matchCompactU32_inv hmc] at hx'
              exact hx'.1 u (by simp [hasFreeVar, hasFreeVarList])
            · exact hshm q htl
        rw [hres]
        exact exprNoPrefixGe_simpExpr fuel _ c1 m1 hsha hc1' hm1' (exprNoPrefixGe_letValue_body h)
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      have hb' := exprNoPrefixGe_simpExpr fuel _ _ _ hsha hshc hshm (exprNoPrefixGe_letValue_body h)
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [hasFreeVar, Bool.or_eq_true, Bool.and_eq_true] at hv
        rcases hv with h1 | ⟨_, h2⟩
        · exact hx'.1 v h1
        · exact hb'.1 v h2
      · simp only [hasBoundVar, Bool.or_eq_true] at hv
        rcases hv with (h0 | h1) | h2
        · exact h.2 v (by simp only [hasBoundVar, h0, Bool.true_or])
        · exact hx'.2 v h1
        · exact hb'.2 v h2
  | fuel, a, c, m, .matchValue s arms, ha, hc, hm, h => by
    have hs' := exprNoPrefixGe_simpExpr fuel a c m ha hc hm (exprNoPrefixGe_matchValue_scrut h)
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', enumTy, nm, fvs, binds, armBody, rfl, hsrc, hpick, _, _, hres⟩
    · rw [hres]
      have ha' := armsNoPrefixGe_simpArms fuel a c m ha hc hm (armsNoPrefixGe_matchValue h)
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simp only [hasFreeVar, Bool.or_eq_true] at hv
        rcases hv with h1 | h2
        · exact hs'.1 v h1
        · exact ha'.1 v h2
      · simp only [hasBoundVar, Bool.or_eq_true] at hv
        rcases hv with h1 | h2
        · exact hs'.2 v h1
        · exact ha'.2 v h2
    · rw [hres]
      obtain ⟨p, hmem, hcase⟩ := pickCtorArm_mem hpick
      have hfvsNp : ∀ fv ∈ fvs, NoPrefixGe cnt fv := by
        rcases hsrc with ⟨v, _, hlk⟩ | ⟨args, hscEq, hav⟩
        · exact hc _ (mem_of_lookup_eq_some hlk)
        · rw [hscEq, allVarNames_inv hav] at hs'
          intro fv hfv
          have hfvFree : hasFreeVar fv (.construct enumTy (some []) nm (fvs.map Aiur.Generic.Expr.var)) = true := by
            simp only [hasFreeVar]
            have hmemFvs : fv ∈ fvs := hfv
            clear hs' hscEq hav h hres hpick hcase hfv
            induction fvs with
            | nil => cases hmemFvs
            | cons f0 fs ih =>
              simp only [List.map_cons, hasFreeVarList, hasFreeVar, Bool.or_eq_true, beq_iff_eq]
              rcases List.mem_cons.mp hmemFvs with rfl | htl
              · exact Or.inl rfl
              · exact Or.inr (ih htl)
          exact hs'.1 fv hfvFree
      have ha1 : ∀ q ∈ binds ++ a.filter (fun q => !(binds.map Prod.fst).contains q.1), NoPrefixGe cnt q.2 := by
        intro q hq
        rcases List.mem_append.mp hq with h1 | h2
        · rcases hcase with ⟨_, rfl⟩ | ⟨pats, _, _, hmp⟩
          · cases h1
          · exact hfvsNp q.2 (matchCtorPats_snd_mem hmp q h1)
        · exact ha q (List.mem_filter.mp h2).1
      exact exprNoPrefixGe_simpExpr fuel' _ c m ha1 hc hm
        (armsNoPrefixGe_mem (armsNoPrefixGe_matchValue h) hmem)
termination_by fuel _ _ _ e _ _ _ _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem listNoPrefixGe_simpExprList {cnt : Nat} :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {xs : List Expr},
      (∀ q ∈ a, NoPrefixGe cnt q.2) →
      (∀ q ∈ c, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv) →
      (∀ q ∈ m, NoPrefixGe cnt q.2) →
      ListNoPrefixGe cnt xs →
      ListNoPrefixGe cnt (simpExprList fuel a c m xs)
  | _, _, _, _, [], _, _, _, h => by rw [simpExprList]; exact h
  | fuel, a, c, m, x :: xs, ha, hc, hm, h => by
    have hx := exprNoPrefixGe_simpExpr fuel a c m ha hc hm (e := x)
      ⟨fun v hv => h.1 v (by simp [hasFreeVarList, hv]), fun v hv => h.2 v (by simp [hasBoundVarList, hv])⟩
    have hxs := listNoPrefixGe_simpExprList fuel a c m ha hc hm (xs := xs)
      ⟨fun v hv => h.1 v (by simp [hasFreeVarList, hv]), fun v hv => h.2 v (by simp [hasBoundVarList, hv])⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp only [simpExprList, hasFreeVarList, Bool.or_eq_true] at hv
      rcases hv with h1 | h2
      · exact hx.1 v h1
      · exact hxs.1 v h2
    · simp only [simpExprList, hasBoundVarList, Bool.or_eq_true] at hv
      rcases hv with h1 | h2
      · exact hx.2 v h1
      · exact hxs.2 v h2
termination_by fuel _ _ _ xs _ _ _ _ => (fuel, sizeOf xs)

theorem armsNoPrefixGe_simpArms {cnt : Nat} :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {arms : List (Pat × Expr)},
      (∀ q ∈ a, NoPrefixGe cnt q.2) →
      (∀ q ∈ c, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv) →
      (∀ q ∈ m, NoPrefixGe cnt q.2) →
      ArmsNoPrefixGe cnt arms →
      ArmsNoPrefixGe cnt (simpArms fuel a c m arms)
  | _, _, _, _, [], _, _, _, h => by rw [simpArms]; exact h
  | fuel, a, c, m, (p, b) :: rest, ha, hc, hm, h => by
    have hsha : ∀ q ∈ (shadowMaps (patBoundVars p) a c m).1, NoPrefixGe cnt q.2 :=
      fun q hq => ha q (List.mem_filter.mp hq).1
    have hshc : ∀ q ∈ (shadowMaps (patBoundVars p) a c m).2.1, ∀ fv ∈ q.2.2.2, NoPrefixGe cnt fv :=
      fun q hq => hc q (List.mem_filter.mp hq).1
    have hshm : ∀ q ∈ (shadowMaps (patBoundVars p) a c m).2.2, NoPrefixGe cnt q.2 :=
      fun q hq => hm q (List.mem_filter.mp hq).1
    have hb := exprNoPrefixGe_simpExpr fuel _ _ _ hsha hshc hshm (exprNoPrefixGe_arm_body h)
    have hr := armsNoPrefixGe_simpArms fuel a c m ha hc hm (armsNoPrefixGe_tail h)
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp only [simpArms, hasFreeVarArms, Bool.or_eq_true, Bool.and_eq_true] at hv
      rcases hv with ⟨_, h1⟩ | h2
      · exact hb.1 v h1
      · exact hr.1 v h2
    · simp only [simpArms, hasBoundVarArms, Bool.or_eq_true] at hv
      rcases hv with (h0 | h1) | h2
      · exact h.2 v (by simp only [hasBoundVarArms, h0, Bool.true_or])
      · exact hb.2 v h1
      · exact hr.2 v h2
termination_by fuel _ _ _ arms _ _ _ _ => (fuel, sizeOf arms)

end

private theorem noInlinableInBoundedCalls_mem_arms {arms : List (Pat × Expr)} {p : Pat} {b : Expr}
    (h : noInlinableInBoundedCallsArms arms = true) (hmem : (p, b) ∈ arms) :
    noInlinableInBoundedCalls b = true := by
  induction arms with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨p0, b0⟩
    simp only [noInlinableInBoundedCallsArms, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact h.1
    · exact ih h.2 htl

mutual

theorem allLitsLt_simpExpr {bound : Nat} :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {e : Expr},
      allLitsLt bound e = true → allLitsLt bound (simpExpr fuel a c m e) = true
  | _, _, _, _, .literal _, h => by rw [simpExpr]; exact h
  | _, _, _, _, .var _, _ | _, _, _, _, .global _ _, _ => by rw [simpExpr]; rfl
  | _, _, _, _, .control _ _, h => by rw [simpExpr]; exact h
  | fuel, a, c, m, .tuple xs, h | fuel, a, c, m, .array xs, h
  | fuel, a, c, m, .construct _ _ _ xs, h | fuel, a, c, m, .constructAs _ _ _ xs, h
  | fuel, a, c, m, .record _ xs, h | fuel, a, c, m, .update _ xs, h
  | fuel, a, c, m, .builtin _ xs, h => by rw [simpExpr]; exact allLitsLtList_simpExprList fuel a c m h
  | fuel, a, c, m, .repeat x _, h | fuel, a, c, m, .index x _, h | fuel, a, c, m, .slice x _ _, h
  | fuel, a, c, m, .member x _, h | fuel, a, c, m, .project x _, h | fuel, a, c, m, .store x, h
  | fuel, a, c, m, .load x, h | fuel, a, c, m, .hint _ x _, h | fuel, a, c, m, .neg x, h => by
    rw [simpExpr]; exact allLitsLt_simpExpr fuel a c m (e := x) h
  | fuel, a, c, m, .binary _ l r, h => by
    simp only [simpExpr, allLitsLt, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_simpExpr fuel a c m h.1, allLitsLt_simpExpr fuel a c m h.2⟩
  | fuel, a, c, m, .call nm targs xs, h => by
    rcases simpExpr_call_cases fuel a c m nm targs xs with
      hres | ⟨_, _, ⟨_, _, _, _, _, _, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]; exact allLitsLtList_simpExprList fuel a c m h
    · rw [hres]; rfl
    · rw [hres]
      have hx0' := allLitsLt_simpExpr fuel a c m (by simpa [allLitsLt, allLitsLtList] using h)
      rw [hx0, matchCompactU32_inv hmc] at hx0'
      simpa [allLitsLt, allLitsLtList] using hx0'
  | fuel, a, c, m, .letValue p x b, h => by
    simp only [allLitsLt, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨_, _, _, hres⟩ | ⟨c1, m1, _, _, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres]; exact allLitsLt_simpExpr fuel _ c m h.2
      · rw [hres]; simp only [allLitsLt, Bool.and_eq_true]
        exact ⟨allLitsLt_simpExpr fuel a c m h.1, allLitsLt_simpExpr fuel _ c1 m1 h.2⟩
      · rw [hres]; exact allLitsLt_simpExpr fuel a c m h.1
      · rw [hres]; exact allLitsLt_simpExpr fuel _ c1 m1 h.2
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      simp only [allLitsLt, Bool.and_eq_true]
      exact ⟨allLitsLt_simpExpr fuel a c m h.1, allLitsLt_simpExpr fuel _ _ _ h.2⟩
  | fuel, a, c, m, .matchValue s arms, h => by
    simp only [allLitsLt, Bool.and_eq_true] at h
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', _, _, _, _, armBody, rfl, _, hpick, _, _, hres⟩
    · rw [hres]; simp only [allLitsLt, Bool.and_eq_true]
      exact ⟨allLitsLt_simpExpr fuel a c m h.1, allLitsLtArms_simpArms fuel a c m h.2⟩
    · rw [hres]
      obtain ⟨p, hmem, _⟩ := pickCtorArm_mem hpick
      exact allLitsLt_simpExpr fuel' _ c m (allLitsLt_mem_arms h.2 hmem)
termination_by fuel _ _ _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem allLitsLtList_simpExprList {bound : Nat} :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {xs : List Expr},
      allLitsLtList bound xs = true → allLitsLtList bound (simpExprList fuel a c m xs) = true
  | _, _, _, _, [], _ => by rw [simpExprList]; rfl
  | fuel, a, c, m, x :: xs, h => by
    simp only [simpExprList, allLitsLtList, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_simpExpr fuel a c m h.1, allLitsLtList_simpExprList fuel a c m h.2⟩
termination_by fuel _ _ _ xs _ => (fuel, sizeOf xs)

theorem allLitsLtArms_simpArms {bound : Nat} :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {arms : List (Pat × Expr)},
      allLitsLtArms bound arms = true → allLitsLtArms bound (simpArms fuel a c m arms) = true
  | _, _, _, _, [], _ => by rw [simpArms]; rfl
  | fuel, a, c, m, (_, b) :: rest, h => by
    simp only [simpArms, allLitsLtArms, Bool.and_eq_true] at h ⊢
    exact ⟨allLitsLt_simpExpr fuel _ _ _ h.1, allLitsLtArms_simpArms fuel a c m h.2⟩
termination_by fuel _ _ _ arms _ => (fuel, sizeOf arms)

end

mutual

theorem noInlinableCalls_simpExpr :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {e : Expr},
      noInlinableCalls e = true → noInlinableCalls (simpExpr fuel a c m e) = true
  | _, _, _, _, .literal _, _ | _, _, _, _, .var _, _ | _, _, _, _, .global _ _, _ => by rw [simpExpr]; rfl
  | _, _, _, _, .control _ _, h => by rw [simpExpr]; exact h
  | fuel, a, c, m, .tuple xs, h | fuel, a, c, m, .array xs, h
  | fuel, a, c, m, .construct _ _ _ xs, h | fuel, a, c, m, .constructAs _ _ _ xs, h
  | fuel, a, c, m, .record _ xs, h | fuel, a, c, m, .update _ xs, h
  | fuel, a, c, m, .builtin _ xs, h => by rw [simpExpr]; exact noInlinableCallsList_simpExprList fuel a c m h
  | fuel, a, c, m, .repeat x _, h | fuel, a, c, m, .index x _, h | fuel, a, c, m, .slice x _ _, h
  | fuel, a, c, m, .member x _, h | fuel, a, c, m, .project x _, h | fuel, a, c, m, .store x, h
  | fuel, a, c, m, .load x, h | fuel, a, c, m, .hint _ x _, h | fuel, a, c, m, .neg x, h => by
    rw [simpExpr]; exact noInlinableCalls_simpExpr fuel a c m (e := x) h
  | fuel, a, c, m, .binary _ l r, h => by
    simp only [simpExpr, noInlinableCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_simpExpr fuel a c m h.1, noInlinableCalls_simpExpr fuel a c m h.2⟩
  | fuel, a, c, m, .call nm targs xs, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    rcases simpExpr_call_cases fuel a c m nm targs xs with
      hres | ⟨_, _, ⟨_, _, _, _, _, _, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]; simp only [noInlinableCalls, Bool.and_eq_true]
      exact ⟨h.1, noInlinableCallsList_simpExprList fuel a c m h.2⟩
    · rw [hres]; rfl
    · rw [hres]
      have hx0' := noInlinableCalls_simpExpr fuel a c m (by simpa [noInlinableCallsList] using h.2)
      rw [hx0, matchCompactU32_inv hmc] at hx0'
      simp only [noInlinableCalls, noInlinableCallsList, Bool.and_eq_true] at hx0'
      exact hx0'.2.1.2.1
  | fuel, a, c, m, .letValue p x b, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨_, _, _, hres⟩ | ⟨c1, m1, _, _, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres]; exact noInlinableCalls_simpExpr fuel _ c m h.2
      · rw [hres]; simp only [noInlinableCalls, Bool.and_eq_true]
        exact ⟨noInlinableCalls_simpExpr fuel a c m h.1, noInlinableCalls_simpExpr fuel _ c1 m1 h.2⟩
      · rw [hres]; exact noInlinableCalls_simpExpr fuel a c m h.1
      · rw [hres]; exact noInlinableCalls_simpExpr fuel _ c1 m1 h.2
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      simp only [noInlinableCalls, Bool.and_eq_true]
      exact ⟨noInlinableCalls_simpExpr fuel a c m h.1, noInlinableCalls_simpExpr fuel _ _ _ h.2⟩
  | fuel, a, c, m, .matchValue s arms, h => by
    simp only [noInlinableCalls, Bool.and_eq_true] at h
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', _, _, _, _, armBody, rfl, _, hpick, _, _, hres⟩
    · rw [hres]; simp only [noInlinableCalls, Bool.and_eq_true]
      exact ⟨noInlinableCalls_simpExpr fuel a c m h.1, noInlinableCallsArms_simpArms fuel a c m h.2⟩
    · rw [hres]
      obtain ⟨p, hmem, _⟩ := pickCtorArm_mem hpick
      exact noInlinableCalls_simpExpr fuel' _ c m (noInlinableCalls_mem_arms h.2 hmem)
termination_by fuel _ _ _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem noInlinableCallsList_simpExprList :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {xs : List Expr},
      noInlinableCallsList xs = true → noInlinableCallsList (simpExprList fuel a c m xs) = true
  | _, _, _, _, [], _ => by rw [simpExprList]; rfl
  | fuel, a, c, m, x :: xs, h => by
    simp only [simpExprList, noInlinableCallsList, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_simpExpr fuel a c m h.1, noInlinableCallsList_simpExprList fuel a c m h.2⟩
termination_by fuel _ _ _ xs _ => (fuel, sizeOf xs)

theorem noInlinableCallsArms_simpArms :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {arms : List (Pat × Expr)},
      noInlinableCallsArms arms = true → noInlinableCallsArms (simpArms fuel a c m arms) = true
  | _, _, _, _, [], _ => by rw [simpArms]; rfl
  | fuel, a, c, m, (_, b) :: rest, h => by
    simp only [simpArms, noInlinableCallsArms, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableCalls_simpExpr fuel _ _ _ h.1, noInlinableCallsArms_simpArms fuel a c m h.2⟩
termination_by fuel _ _ _ arms _ => (fuel, sizeOf arms)

end

mutual

theorem literalsBounded_simpExpr :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {e : Expr},
      literalsBounded e = true → literalsBounded (simpExpr fuel a c m e) = true
  | _, _, _, _, .literal _, _ | _, _, _, _, .var _, _ | _, _, _, _, .global _ _, _ => by rw [simpExpr]; rfl
  | _, _, _, _, .control _ _, h => by rw [simpExpr]; exact h
  | fuel, a, c, m, .tuple xs, h | fuel, a, c, m, .array xs, h
  | fuel, a, c, m, .construct _ _ _ xs, h | fuel, a, c, m, .constructAs _ _ _ xs, h
  | fuel, a, c, m, .record _ xs, h | fuel, a, c, m, .update _ xs, h
  | fuel, a, c, m, .builtin _ xs, h => by rw [simpExpr]; exact literalsBoundedList_simpExprList fuel a c m h
  | fuel, a, c, m, .repeat x _, h | fuel, a, c, m, .index x _, h | fuel, a, c, m, .slice x _ _, h
  | fuel, a, c, m, .member x _, h | fuel, a, c, m, .project x _, h | fuel, a, c, m, .store x, h
  | fuel, a, c, m, .load x, h | fuel, a, c, m, .hint _ x _, h | fuel, a, c, m, .neg x, h => by
    rw [simpExpr]; exact literalsBounded_simpExpr fuel a c m (e := x) h
  | fuel, a, c, m, .binary _ l r, h => by
    simp only [simpExpr, literalsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_simpExpr fuel a c m h.1, literalsBounded_simpExpr fuel a c m h.2⟩
  | fuel, a, c, m, .call nm targs xs, h => by
    have hxs' := literalsBoundedList_simpExprList fuel a c m (literalsBounded_call_args h)
    rcases simpExpr_call_cases fuel a c m nm targs xs with
      hres | ⟨_, _, ⟨_, _, _, _, _, _, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]
      cases targs with
      | none => exact hxs'
      | some ts =>
        cases ts with
        | cons _ _ => exact hxs'
        | nil =>
          cases xs with
          | nil => rw [simpExprList]; rfl
          | cons x0 rest =>
            cases rest with
            | cons x1 rest2 => rw [simpExprList, simpExprList] at hxs' ⊢; exact hxs'
            | nil =>
              rw [simpExprList, simpExprList]
              simp only [literalsBounded] at h ⊢
              cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field") with
              | true =>
                rw [h1] at h
                simp only [↓reduceIte, Bool.and_eq_true] at h ⊢
                exact ⟨allLitsLt_simpExpr fuel a c m h.1, literalsBounded_simpExpr fuel a c m h.2⟩
              | false =>
                rw [h1] at h
                simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases h2 : (nm == "UInt32::from_field") with
                | true =>
                  rw [h2] at h
                  simp only [↓reduceIte, Bool.and_eq_true] at h ⊢
                  exact ⟨allLitsLt_simpExpr fuel a c m h.1, literalsBounded_simpExpr fuel a c m h.2⟩
                | false =>
                  rw [h2] at h
                  simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                  exact literalsBounded_simpExpr fuel a c m h
    · rw [hres]; rfl
    · rw [hres]
      have hx0' : literalsBounded (simpExpr fuel a c m x0) = true := by
        simpa [simpExprList, literalsBoundedList] using hxs'
      rw [hx0, matchCompactU32_inv hmc] at hx0'
      simpa [literalsBounded] using hx0'
  | fuel, a, c, m, .letValue p x b, h => by
    simp only [literalsBounded, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨_, _, _, hres⟩ | ⟨c1, m1, _, _, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres]; exact literalsBounded_simpExpr fuel _ c m h.2
      · rw [hres]; simp only [literalsBounded, Bool.and_eq_true]
        exact ⟨literalsBounded_simpExpr fuel a c m h.1, literalsBounded_simpExpr fuel _ c1 m1 h.2⟩
      · rw [hres]; exact literalsBounded_simpExpr fuel a c m h.1
      · rw [hres]; exact literalsBounded_simpExpr fuel _ c1 m1 h.2
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      simp only [literalsBounded, Bool.and_eq_true]
      exact ⟨literalsBounded_simpExpr fuel a c m h.1, literalsBounded_simpExpr fuel _ _ _ h.2⟩
  | fuel, a, c, m, .matchValue s arms, h => by
    simp only [literalsBounded, Bool.and_eq_true] at h
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', _, _, _, _, armBody, rfl, _, hpick, _, _, hres⟩
    · rw [hres]; simp only [literalsBounded, Bool.and_eq_true]
      exact ⟨literalsBounded_simpExpr fuel a c m h.1, literalsBoundedArms_simpArms fuel a c m h.2⟩
    · rw [hres]
      obtain ⟨p, hmem, _⟩ := pickCtorArm_mem hpick
      exact literalsBounded_simpExpr fuel' _ c m (literalsBounded_mem_arms h.2 hmem)
termination_by fuel _ _ _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem literalsBoundedList_simpExprList :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {xs : List Expr},
      literalsBoundedList xs = true → literalsBoundedList (simpExprList fuel a c m xs) = true
  | _, _, _, _, [], _ => by rw [simpExprList]; rfl
  | fuel, a, c, m, x :: xs, h => by
    simp only [simpExprList, literalsBoundedList, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_simpExpr fuel a c m h.1, literalsBoundedList_simpExprList fuel a c m h.2⟩
termination_by fuel _ _ _ xs _ => (fuel, sizeOf xs)

theorem literalsBoundedArms_simpArms :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {arms : List (Pat × Expr)},
      literalsBoundedArms arms = true → literalsBoundedArms (simpArms fuel a c m arms) = true
  | _, _, _, _, [], _ => by rw [simpArms]; rfl
  | fuel, a, c, m, (_, b) :: rest, h => by
    simp only [simpArms, literalsBoundedArms, Bool.and_eq_true] at h ⊢
    exact ⟨literalsBounded_simpExpr fuel _ _ _ h.1, literalsBoundedArms_simpArms fuel a c m h.2⟩
termination_by fuel _ _ _ arms _ => (fuel, sizeOf arms)

end

mutual

theorem noInlinableInBoundedCalls_simpExpr :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {e : Expr},
      noInlinableInBoundedCalls e = true →
      noInlinableInBoundedCalls (simpExpr fuel a c m e) = true
  | _, _, _, _, .literal _, _ | _, _, _, _, .var _, _ | _, _, _, _, .global _ _, _ => by rw [simpExpr]; rfl
  | _, _, _, _, .control _ _, h => by rw [simpExpr]; exact h
  | fuel, a, c, m, .tuple xs, h | fuel, a, c, m, .array xs, h
  | fuel, a, c, m, .construct _ _ _ xs, h | fuel, a, c, m, .constructAs _ _ _ xs, h
  | fuel, a, c, m, .record _ xs, h | fuel, a, c, m, .update _ xs, h
  | fuel, a, c, m, .builtin _ xs, h => by rw [simpExpr]; exact noInlinableInBoundedCallsList_simpExprList fuel a c m h
  | fuel, a, c, m, .repeat x _, h | fuel, a, c, m, .index x _, h | fuel, a, c, m, .slice x _ _, h
  | fuel, a, c, m, .member x _, h | fuel, a, c, m, .project x _, h | fuel, a, c, m, .store x, h
  | fuel, a, c, m, .load x, h | fuel, a, c, m, .hint _ x _, h | fuel, a, c, m, .neg x, h => by
    rw [simpExpr]; exact noInlinableInBoundedCalls_simpExpr fuel a c m (e := x) h
  | fuel, a, c, m, .binary _ l r, h => by
    simp only [simpExpr, noInlinableInBoundedCalls, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_simpExpr fuel a c m h.1, noInlinableInBoundedCalls_simpExpr fuel a c m h.2⟩
  | fuel, a, c, m, .call nm targs xs, h => by
    have hxs' := noInlinableInBoundedCallsList_simpExprList fuel a c m (noInlinableInBoundedCalls_call_args h)
    rcases simpExpr_call_cases fuel a c m nm targs xs with
      hres | ⟨_, _, ⟨_, _, _, _, _, _, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]
      cases targs with
      | none => exact hxs'
      | some ts =>
        cases ts with
        | cons _ _ => exact hxs'
        | nil =>
          cases xs with
          | nil => rw [simpExprList]; rfl
          | cons x0 rest =>
            cases rest with
            | cons x1 rest2 => rw [simpExprList, simpExprList] at hxs' ⊢; exact hxs'
            | nil =>
              rw [simpExprList, simpExprList]
              simp only [noInlinableInBoundedCalls] at h ⊢
              cases h1 : (nm == "u32_of_field" || nm == "Prog::u32_of_field" || nm == "UInt32::from_field") with
              | true =>
                rw [h1] at h; simp only [↓reduceIte] at h ⊢
                exact noInlinableCalls_simpExpr fuel a c m h
              | false =>
                rw [h1] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
                exact noInlinableInBoundedCalls_simpExpr fuel a c m h
    · rw [hres]; rfl
    · rw [hres]
      have hx0' : noInlinableInBoundedCalls (simpExpr fuel a c m x0) = true := by
        simpa [simpExprList, noInlinableInBoundedCallsList] using hxs'
      rw [hx0, matchCompactU32_inv hmc] at hx0'
      simpa [noInlinableInBoundedCalls] using hx0'
  | fuel, a, c, m, .letValue p x b, h => by
    simp only [noInlinableInBoundedCalls, Bool.and_eq_true] at h
    cases p with
    | bind nm =>
      rcases simpExpr_letValue_bind_cases fuel a c m nm x b with
        ⟨_, _, _, hres⟩ | ⟨c1, m1, _, _, hres | ⟨hres, _⟩ | ⟨hres, _, _⟩⟩
      · rw [hres]; exact noInlinableInBoundedCalls_simpExpr fuel _ c m h.2
      · rw [hres]; simp only [noInlinableInBoundedCalls, Bool.and_eq_true]
        exact ⟨noInlinableInBoundedCalls_simpExpr fuel a c m h.1, noInlinableInBoundedCalls_simpExpr fuel _ c1 m1 h.2⟩
      · rw [hres]; exact noInlinableInBoundedCalls_simpExpr fuel a c m h.1
      · rw [hres]; exact noInlinableInBoundedCalls_simpExpr fuel _ c1 m1 h.2
    | wildcard | literal _ | global _ _ | load _ | orElse _ _ _ | tuple _ | array _
    | «repeat» _ _ | record _ _ | construct _ _ _ | constructAs _ _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      simp only [noInlinableInBoundedCalls, Bool.and_eq_true]
      exact ⟨noInlinableInBoundedCalls_simpExpr fuel a c m h.1, noInlinableInBoundedCalls_simpExpr fuel _ _ _ h.2⟩
  | fuel, a, c, m, .matchValue s arms, h => by
    simp only [noInlinableInBoundedCalls, Bool.and_eq_true] at h
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', _, _, _, _, armBody, rfl, _, hpick, _, _, hres⟩
    · rw [hres]; simp only [noInlinableInBoundedCalls, Bool.and_eq_true]
      exact ⟨noInlinableInBoundedCalls_simpExpr fuel a c m h.1, noInlinableInBoundedCallsArms_simpArms fuel a c m h.2⟩
    · rw [hres]
      obtain ⟨p, hmem, _⟩ := pickCtorArm_mem hpick
      exact noInlinableInBoundedCalls_simpExpr fuel' _ c m (noInlinableInBoundedCalls_mem_arms h.2 hmem)
termination_by fuel _ _ _ e _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals try simp only [List.cons.sizeOf_spec]
  all_goals omega

theorem noInlinableInBoundedCallsList_simpExprList :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {xs : List Expr},
      noInlinableInBoundedCallsList xs = true →
      noInlinableInBoundedCallsList (simpExprList fuel a c m xs) = true
  | _, _, _, _, [], _ => by rw [simpExprList]; rfl
  | fuel, a, c, m, x :: xs, h => by
    simp only [simpExprList, noInlinableInBoundedCallsList, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_simpExpr fuel a c m h.1, noInlinableInBoundedCallsList_simpExprList fuel a c m h.2⟩
termination_by fuel _ _ _ xs _ => (fuel, sizeOf xs)

theorem noInlinableInBoundedCallsArms_simpArms :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap) {arms : List (Pat × Expr)},
      noInlinableInBoundedCallsArms arms = true →
      noInlinableInBoundedCallsArms (simpArms fuel a c m arms) = true
  | _, _, _, _, [], _ => by rw [simpArms]; rfl
  | fuel, a, c, m, (_, b) :: rest, h => by
    simp only [simpArms, noInlinableInBoundedCallsArms, Bool.and_eq_true] at h ⊢
    exact ⟨noInlinableInBoundedCalls_simpExpr fuel _ _ _ h.1, noInlinableInBoundedCallsArms_simpArms fuel a c m h.2⟩
termination_by fuel _ _ _ arms _ => (fuel, sizeOf arms)

end

/-! ### Part 8C: Typing Preservation under `simpExpr` (`hasTy_simpExpr`) -/

/-- Typing invariant on `aliases`, `ctors`, `compacts` during `simpExpr`. -/
def AliasTyInv (aliases : AliasMap) (ΓOrig ΓOpt : TyEnv) (e : Expr) : Prop :=
  (∀ q ∈ aliases, hasBoundVar q.2 e = false) ∧
  (∀ x, hasFreeVar x e = true → ΓOrig.lookup x = ΓOpt.lookup (resolveAlias aliases x))

def AliasTyInvList (aliases : AliasMap) (ΓOrig ΓOpt : TyEnv) (xs : List Expr) : Prop :=
  (∀ q ∈ aliases, hasBoundVarList q.2 xs = false) ∧
  (∀ x, hasFreeVarList x xs = true → ΓOrig.lookup x = ΓOpt.lookup (resolveAlias aliases x))

def AliasTyInvArms (aliases : AliasMap) (ΓOrig ΓOpt : TyEnv) (arms : List (Pat × Expr)) : Prop :=
  (∀ q ∈ aliases, hasBoundVarArms q.2 arms = false) ∧
  (∀ x, hasFreeVarArms x arms = true → ΓOrig.lookup x = ΓOpt.lookup (resolveAlias aliases x))

def CtorTyInv (ctors : CtorMap) (enums : List Aiur.Generic.EnumDecl) (ΓOpt : TyEnv) : Prop :=
  ∀ v en nm fvs, (v, (en, nm, fvs)) ∈ ctors →
    ΓOpt.lookup v = some (.named en []) ∧
    ∃ fts, findCtorFields enums en nm = some fts ∧
      List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs fts

def CompactTyInv (compacts : AliasMap) (ΓOpt : TyEnv) : Prop :=
  ∀ t u, (t, u) ∈ compacts → ΓOpt.lookup u = some u32Ty

private theorem ctorTyInv_shadow {ctors : CtorMap} {enums : List Aiur.Generic.EnumDecl}
    {ΓOpt Δ : TyEnv} {bs : List String} {a : AliasMap} {m : AliasMap}
    (hc : CtorTyInv ctors enums ΓOpt) (hdom : Δ.map Prod.fst = bs) :
    CtorTyInv (shadowMaps bs a ctors m).2.1 enums (Δ ++ ΓOpt) := by
  intro v en nm fvs hmem
  obtain ⟨hmemOrig, hfilt⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hfilt
  have hvNot : v ∉ bs := fun hm => by
    have := List.contains_iff_mem.mpr hm; rw [this] at hfilt; cases hfilt.1
  obtain ⟨hvTy, fts, hctor, hall⟩ := hc v en nm fvs hmemOrig
  refine ⟨by rw [lookup_append_of_not_mem_poly (hdom ▸ hvNot)]; exact hvTy, fts, hctor, ?_⟩
  have hnotAll : ∀ fv ∈ fvs, fv ∉ bs := fun fv hfv hm => by
    have h1 := hfilt.2 fv hfv
    have h2 := List.contains_iff_mem.mpr hm
    rw [h2] at h1; cases h1
  clear hfilt hmem hmemOrig hvNot hvTy hctor hc
  induction hall with
  | nil => exact .nil
  | @cons fv ft fvs' fts' hfv _ ih =>
    refine .cons ?_ (ih fun u hu => hnotAll u (List.mem_cons_of_mem _ hu))
    rw [lookup_append_of_not_mem_poly (hdom ▸ hnotAll fv List.mem_cons_self)]
    exact hfv

private theorem compactTyInv_shadow {compacts : AliasMap} {ΓOpt Δ : TyEnv}
    {bs : List String} {a : AliasMap} {c : CtorMap}
    (hm : CompactTyInv compacts ΓOpt) (hdom : Δ.map Prod.fst = bs) :
    CompactTyInv (shadowMaps bs a c compacts).2.2 (Δ ++ ΓOpt) := by
  intro t u hmem
  obtain ⟨hmemOrig, hfilt⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfilt
  have huNot : u ∉ bs := fun h => by
    have := List.contains_iff_mem.mpr h; rw [this] at hfilt; cases hfilt.2
  rw [lookup_append_of_not_mem_poly (hdom ▸ huNot)]
  exact hm t u hmemOrig

private theorem aliasTyInv_shadow {aliases : AliasMap} {ctors : CtorMap} {compacts : AliasMap}
    {ΓOrig ΓOpt Δ : TyEnv} {p : Pat} {b : Expr}
    (hdom : Δ.map Prod.fst = patBoundVars p)
    (hno2 : ∀ q ∈ aliases, q.2 ∉ patBoundVars p ∧ hasBoundVar q.2 b = false)
    (hfree : ∀ x, x ∉ patBoundVars p → hasFreeVar x b = true →
      ΓOrig.lookup x = ΓOpt.lookup (resolveAlias aliases x)) :
    AliasTyInv (shadowMaps (patBoundVars p) aliases ctors compacts).1 (Δ ++ ΓOrig) (Δ ++ ΓOpt) b := by
  refine ⟨fun q hq => (hno2 q (List.mem_filter.mp hq).1).2, fun x hfx => ?_⟩
  rw [resolveAlias_shadowMaps (patBoundVars p) aliases ctors compacts (fun q hq => (hno2 q hq).1)]
  by_cases hx : x ∈ patBoundVars p
  · simp only [hx, ↓reduceIte]
    rw [lookup_append_of_mem_poly (hdom ▸ hx), lookup_append_of_mem_poly (hdom ▸ hx)]
  · simp only [hx, ↓reduceIte]
    have hrNot : resolveAlias aliases x ∉ patBoundVars p := by
      unfold resolveAlias
      cases hl : aliases.lookup x with
      | none => exact hx
      | some y => exact (hno2 (x, y) (mem_of_lookup_eq_some hl)).1
    rw [lookup_append_of_not_mem_poly (hdom ▸ hx), lookup_append_of_not_mem_poly (hdom ▸ hrNot)]
    exact hfree x hx hfx

private theorem hasTyList_map_var_inv {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl} {Γ : TyEnv} :
    ∀ {fvs : List String} {fts : List Lower.Ty},
      HasTyList sigs enums Γ (fvs.map Aiur.Generic.Expr.var) fts →
      List.Forall₂ (fun fv ft => Γ.lookup fv = some ft) fvs fts
  | [], _, .nil => .nil
  | _ :: _, _, .cons (.var hl) tl => .cons hl (hasTyList_map_var_inv tl)

private theorem hasTy_compactU32_inv {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {e inner : Expr} {t : Lower.Ty}
    (hmc : matchCompactU32 e = some inner)
    (hty : HasTy (fnSigsOf fns) enums Γ e t) :
    t = .field ∧ HasTy (fnSigsOf fns) enums Γ inner u32Ty := by
  rw [matchCompactU32_inv hmc] at hty
  cases hty with | call hsig1 items1 =>
  cases items1 with | cons hcmp items1' =>
  cases items1'
  rw [show qualifyName "UInt32::compact_field" = "UInt32::compact_field" from rfl,
      fnSigsOf_nonProg fns rfl] at hsig1
  injection hsig1 with hsig1; cases hsig1
  cases hcmp with | call hsig2 items2 =>
  cases items2 with | cons hinner items2' =>
  cases items2'
  rw [show qualifyName "UInt32::compact" = "UInt32::compact" from rfl,
      fnSigsOf_nonProg fns rfl] at hsig2
  injection hsig2 with hsig2; cases hsig2
  exact ⟨rfl, hinner⟩

private theorem patListHasTy_matchCtorPats {enums : List Aiur.Generic.EnumDecl} {ΓOpt : TyEnv} :
    ∀ {pats : List Pat} {fts : List Lower.Ty} {Δ : TyEnv} {fvs : List String} {binds : AliasMap},
      PatListHasTy enums pats fts Δ →
      matchCtorPats pats fvs = some binds →
      List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs fts →
      Δ.map Prod.fst = binds.map Prod.fst ∧
      (∀ v, (binds.lookup v).isSome →
        ∃ fv, binds.lookup v = some fv ∧ Δ.lookup v = ΓOpt.lookup fv)
  | [], _, _, [], _, .nil, hm, .nil => by
    simp only [matchCtorPats, Option.some.injEq] at hm; subst hm
    exact ⟨rfl, fun _ h => by simp at h⟩
  | .bind v :: ps, ft :: fts, _, fv :: fvs, binds, .cons .bind tl, hm, .cons hfv hrest => by
    simp only [matchCtorPats] at hm
    cases hr : matchCtorPats ps fvs with
    | none => rw [hr] at hm; cases hm
    | some bs =>
      rw [hr] at hm; simp only [Option.map_some, Option.some.injEq] at hm; subst hm
      obtain ⟨hdom, hlook⟩ := patListHasTy_matchCtorPats tl hr hrest
      refine ⟨by simp [hdom], fun x hx => ?_⟩
      by_cases hxv : x = v
      · subst hxv; exact ⟨fv, by simp [List.lookup], by simp [hfv]⟩
      · simp only [List.lookup, beq_false_of_ne hxv] at hx ⊢
        obtain ⟨fv0, hlk, heq⟩ := hlook x hx
        exact ⟨fv0, hlk, by simp [List.lookup, beq_false_of_ne hxv, heq]⟩
  | .wildcard :: ps, ft :: fts, _, fv :: fvs, binds, .cons .wildcard tl, hm, .cons _ hrest => by
    simp only [matchCtorPats] at hm
    obtain ⟨hdom, hlook⟩ := patListHasTy_matchCtorPats tl hm hrest
    exact ⟨by simpa using hdom, hlook⟩
  | .literal _ :: _, _, _, _, _, _, hm, _ | .tuple _ :: _, _, _, _, _, _, hm, _
  | .array _ :: _, _, _, _, _, _, hm, _ | .construct _ _ _ :: _, _, _, _, _, _, hm, _
  | .global _ _ :: _, _, _, _, _, _, hm, _ | .load _ :: _, _, _, _, _, _, hm, _
  | .orElse _ _ _ :: _, _, _, _, _, _, hm, _ | .repeat _ _ :: _, _, _, _, _, _, hm, _
  | .record _ _ :: _, _, _, _, _, _, hm, _ | .constructAs _ _ _ _ :: _, _, _, _, _, _, hm, _ => by
    simp [matchCtorPats] at hm

private theorem hasTy_drop_bind_fnSigs {sigs : FnSigs} {enums : List Aiur.Generic.EnumDecl}
    {Γ : TyEnv} {v : String} {tv tb : Lower.Ty} {b : Expr}
    (hb : HasTy sigs enums ((v, tv) :: Γ) b tb) (hnot : hasFreeVar v b = false) :
    HasTy sigs enums Γ b tb := by
  refine hasTy_envAgree hb fun x hx => ?_
  have hne : x ≠ v := by intro heq; subst heq; rw [hnot] at hx; cases hx
  simp [List.lookup, beq_false_of_ne hne]

private theorem not_mem_map_fst_of_lookup_none {α : Type} {z : String} :
    ∀ {xs : List (String × α)}, xs.lookup z = none → z ∉ xs.map Prod.fst
  | [], _, hm => by cases hm
  | (k, _) :: tl, hnone, hm => by
    simp only [List.lookup] at hnone
    by_cases hzk : z = k
    · subst hzk; simp at hnone
    · simp only [beq_false_of_ne hzk] at hnone
      simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | htl
      · exact hzk rfl
      · exact not_mem_map_fst_of_lookup_none hnone htl

mutual

/-- Typing preservation for `simpExpr`! -/
theorem hasTy_simpExpr {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap)
      {ΓOrig ΓOpt : TyEnv} {e : Expr} {t : Lower.Ty},
      AliasTyInv a ΓOrig ΓOpt e →
      CtorTyInv c enums ΓOpt →
      CompactTyInv m ΓOpt →
      HasTy (fnSigsOf fns) enums ΓOrig e t →
      HasTy (fnSigsOf fns) enums ΓOpt (simpExpr fuel a c m e) t
  | _, _, _, _, _, _, _, _, _, _, _, .literal => by rw [simpExpr]; exact .literal
  | _, a, _, _, _, _, .var x, _, ha, _, _, .var hl => by
    simp only [simpExpr]
    exact .var (by rw [← ha.2 x (by simp [hasFreeVar])]; exact hl)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .tuple items => by
    rw [simpExpr]; exact .tuple (hasTyList_simpExprList hSigs fuel a c m ha hc hm items)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .array hlen items => by
    rw [simpExpr]
    exact .array (by rw [simpExprList_length]; exact hlen) (hasTyList_simpExprList hSigs fuel a c m ha hc hm items)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .repeat hx => by
    rw [simpExpr]; exact .repeat (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .index hx => by
    rw [simpExpr]; exact .index (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .project hx hget => by
    rw [simpExpr]; exact .project (hasTy_simpExpr hSigs fuel a c m ha hc hm hx) hget
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .slice hnot hx => by
    rw [simpExpr]; exact .slice hnot (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .construct h1 h2 h3 h4 hctor items => by
    rw [simpExpr]; exact .construct h1 h2 h3 h4 hctor (hasTyList_simpExprList hSigs fuel a c m ha hc hm items)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .builtin items => by
    rw [simpExpr]; exact .builtin (hasTyList_simpExprList hSigs fuel a c m ha hc hm items)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .store hx => by
    rw [simpExpr]; exact .store (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .load hx => by
    rw [simpExpr]; exact .load (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .hint hfo hx => by
    rw [simpExpr]; exact .hint hfo (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .neg hx => by
    rw [simpExpr]; exact .neg (hasTy_simpExpr hSigs fuel a c m ha hc hm hx)
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .binary hl hr => by
    rw [simpExpr]
    exact .binary
      (hasTy_simpExpr hSigs fuel a c m
        ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1,
         fun x hx => ha.2 x (by simp [hasFreeVar, hx])⟩ hc hm hl)
      (hasTy_simpExpr hSigs fuel a c m
        ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.2,
         fun x hx => ha.2 x (by simp [hasFreeVar, hx])⟩ hc hm hr)
  | fuel, a, c, m, _, _, .call nm (some []) xs, t, ha, hc, hm, .call hsig items => by
    have hxs' := hasTyList_simpExprList hSigs fuel a c m ha hc hm items
    rcases simpExpr_call_cases fuel a c m nm (some []) xs with
      hres | ⟨hnm, _, ⟨x0, tvar, u, rfl, _, hlk, hres⟩ | ⟨x0, arg, inner, rfl, hx0, hmc, hres⟩⟩
    · rw [hres]; exact .call hsig hxs'
    · rw [hres]
      have ht : t = u32Ty := by
        rcases hnm with rfl | rfl
        · rw [show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl] at hsig
          exact (hSigs.1 _ _ hsig).2
        · rw [show qualifyName "UInt32::from_field" = "UInt32::from_field" from rfl,
              fnSigsOf_nonProg fns rfl] at hsig
          injection hsig with hsig; cases hsig; rfl
      subst ht
      exact .var (hm tvar u (mem_of_lookup_eq_some hlk))
    · rw [hres]
      have ht : t = u32Ty := by
        rcases hnm with rfl | rfl
        · rw [show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl] at hsig
          exact (hSigs.1 _ _ hsig).2
        · rw [show qualifyName "UInt32::from_field" = "UInt32::from_field" from rfl,
              fnSigsOf_nonProg fns rfl] at hsig
          injection hsig with hsig; cases hsig; rfl
      subst ht
      simp only [simpExprList] at hxs'
      cases hxs' with | cons harg _ =>
      rw [hx0] at harg
      exact (hasTy_compactU32_inv hmc harg).2
  | fuel, a, c, m, ΓOrig, ΓOpt, .letValue p x b, tb, ha, hc, hm, .letValue (tx := tx) (Δ := Δ) hx hp hb => by
    have haX : AliasTyInv a ΓOrig ΓOpt x :=
      ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1.2,
       fun z hz => ha.2 z (by simp [hasFreeVar, hz])⟩
    have hx' := hasTy_simpExpr hSigs fuel a c m haX hc hm hx
    have hno2 : ∀ q ∈ a, q.2 ∉ patBoundVars p ∧ hasBoundVar q.2 b = false := by
      intro q hq
      have h0 := ha.1 q hq
      simp only [hasBoundVar, Bool.or_eq_false_iff] at h0
      exact ⟨(fun hmem => by have := List.contains_iff_mem.mpr hmem; rw [this] at h0; cases h0.1.1), h0.2⟩
    have hfreeB : ∀ z, z ∉ patBoundVars p → hasFreeVar z b = true →
        ΓOrig.lookup z = ΓOpt.lookup (resolveAlias a z) :=
      fun z hnot hfz => ha.2 z (by simp [hasFreeVar, hnot, hfz])
    have haB0 := aliasTyInv_shadow (ctors := c) (compacts := m) hp.dom_eq hno2 hfreeB
    have hc0 := ctorTyInv_shadow (a := a) (m := m) hc hp.dom_eq
    have hm0 := compactTyInv_shadow (a := a) (c := c) hm hp.dom_eq
    cases p with
    | bind v =>
      cases hp
      rcases simpExpr_letValue_bind_cases fuel a c m v x b with
        ⟨y, hy, hbvY, hres⟩ | ⟨c1, m1, hc1, hm1, hres⟩
      · rw [hres]
        rw [hy] at hx'
        cases hx' with | var hΓy =>
        refine hasTy_simpExpr hSigs fuel _ c m ?_ hc hm hb
        refine ⟨fun q hq => ?_, fun z hfz => ?_⟩
        · rcases List.mem_cons.mp hq with rfl | htl
          · exact hbvY
          · exact (hno2 q (List.mem_filter.mp htl).1).2
        · rw [resolveAlias_cons_filter]
          by_cases hzv : z = v
          · subst hzv; simp [hΓy]
          · simp only [hzv, ↓reduceIte, List.cons_append, List.nil_append, List.lookup, beq_false_of_ne hzv]
            exact hfreeB z (by simp [patBoundVars, hzv]) hfz
      · have hc1' : CtorTyInv c1 enums ((v, tx) :: ΓOpt) := by
          rcases hc1 with rfl | ⟨ty, nm, args, fvs, hxeq, hav, hvNot, rfl⟩
          · exact hc0
          · intro w en' nm' fvs' hmem
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, hinfo⟩ := Prod.mk.inj heq
              obtain ⟨rfl, rfl, rfl⟩ := hinfo
              rw [hxeq, allVarNames_inv hav] at hx'
              cases hx' with | construct _ _ _ _ hctor items =>
              refine ⟨by simp [List.lookup], _, hctor, ?_⟩
              have hall := hasTyList_map_var_inv items
              clear items hxeq hav hres hmem heq hctor
              induction hall with
              | nil => exact .nil
              | @cons fv ft fvs1 fts1 hfv _ ih =>
                simp only [List.mem_cons, not_or] at hvNot
                exact .cons (by simp [List.lookup, beq_false_of_ne (Ne.symm hvNot.1), hfv]) (ih hvNot.2)
            · exact hc0 w en' nm' fvs' htl
        have hm1' : CompactTyInv m1 ((v, tx) :: ΓOpt) := by
          rcases hm1 with rfl | ⟨u, hmc, huv, rfl⟩
          · exact hm0
          · intro tvar uvar hmem
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
              obtain ⟨_, huTy⟩ := hasTy_compactU32_inv hmc hx'
              cases huTy with | var hΓu =>
              simp [List.lookup, beq_false_of_ne huv, hΓu]
            · exact hm0 tvar uvar htl
        have hb' := hasTy_simpExpr hSigs fuel _ c1 m1 haB0 hc1' hm1' hb
        rcases hres with hres | ⟨hres, hbeq⟩ | ⟨hres, _, hnotFree⟩
        · rw [hres]; exact .letValue hx' .bind hb'
        · rw [hres]
          dsimp only [shadowMaps, patBoundVars] at hb'
          rw [hbeq] at hb'; cases hb' with | var hlv =>
          simp only [List.cons_append, List.nil_append, List.lookup, beq_self_eq_true, Option.some.injEq] at hlv
          subst hlv; exact hx'
        · rw [hres]; exact hasTy_drop_bind_fnSigs hb' hnotFree
    | wildcard | literal _ | tuple _ | array _ | construct _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)]
      exact .letValue hx' hp (hasTy_simpExpr hSigs fuel _ _ _ haB0 hc0 hm0 hb)
    | global _ _ | load _ | orElse _ _ _ | «repeat» _ _ | record _ _ | constructAs _ _ _ _ => cases hp
  | fuel, a, c, m, ΓOrig, ΓOpt, .matchValue s arms, tb, ha, hc, hm, .matchValue (ts := ts) hs harms => by
    have haS : AliasTyInv a ΓOrig ΓOpt s :=
      ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1,
       fun z hz => ha.2 z (by simp [hasFreeVar, hz])⟩
    have haArms : AliasTyInvArms a ΓOrig ΓOpt arms :=
      ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.2,
       fun z hz => ha.2 z (by simp [hasFreeVar, hz])⟩
    have hs' := hasTy_simpExpr hSigs fuel a c m haS hc hm hs
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', enumTy, nm, fvs, binds, armBody, rfl, hsrc, hpick, _, hbvBinds, hres⟩
    · rw [hres]; exact .matchValue hs' (hasTyArms_simpArms hSigs fuel a c m haArms hc hm harms)
    · rw [hres]
      have hknown : ts = .named enumTy [] ∧
          ∃ fts, findCtorFields enums enumTy nm = some fts ∧
            List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs fts := by
        rcases hsrc with ⟨v, hscEq, hlk⟩ | ⟨args, hscEq, hav⟩
        · rw [hscEq] at hs'; cases hs' with | var hΓv =>
          obtain ⟨hvTy, fts, hctor, hall⟩ := hc v enumTy nm fvs (mem_of_lookup_eq_some hlk)
          rw [hΓv, Option.some.injEq] at hvTy
          exact ⟨hvTy, fts, hctor, hall⟩
        · rw [hscEq, allVarNames_inv hav] at hs'
          cases hs' with | construct _ _ _ _ hctor items =>
          exact ⟨rfl, _, hctor, hasTyList_map_var_inv items⟩
      obtain ⟨rfl, fts, hctor, hfvTys⟩ := hknown
      obtain ⟨p, hmem, hcase⟩ := pickCtorArm_mem hpick
      obtain ⟨Δ, hp, hb⟩ := harms.mem hmem
      have harmFree : ∀ z, z ∉ patBoundVars p → hasFreeVar z armBody = true →
          hasFreeVarArms z arms = true := by
        clear hres hpick hfvTys hs' hs haS ha haArms harms
        intro z hnot hfz
        induction arms with
        | nil => cases hmem
        | cons hd tl ih =>
          rcases hd with ⟨p0, b0⟩
          simp only [hasFreeVarArms, Bool.or_eq_true]
          rcases List.mem_cons.mp hmem with heq | htl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact Or.inl (by simp [hnot, hfz])
          · exact Or.inr (ih htl)
      have harmBound : ∀ q ∈ a, hasBoundVar q.2 armBody = false := by
        intro q hq
        cases hbb : hasBoundVar q.2 armBody with
        | false => rfl
        | true =>
          have h0 := haArms.1 q hq
          rw [hasBoundVarArms_of_mem hmem hbb] at h0
          cases h0
      rcases hcase with ⟨rfl, rfl⟩ | ⟨pats, rfl, _, hmp⟩
      · cases hp
        refine hasTy_simpExpr hSigs fuel' _ c m ?_ hc hm hb
        refine ⟨fun q hq => harmBound q (List.mem_filter.mp hq).1, fun z hfz => ?_⟩
        rw [resolveAlias_append_filter]; simp only [List.lookup]
        exact haArms.2 z (harmFree z (by simp [patBoundVars]) hfz)
      · cases hp with | construct _ hctor' pitems =>
        rw [hctor] at hctor'; simp only [Option.some.injEq] at hctor'; subst hctor'
        obtain ⟨hdomB, hlookB⟩ := patListHasTy_matchCtorPats pitems hmp hfvTys
        refine hasTy_simpExpr hSigs fuel' _ c m ?_ hc hm hb
        refine ⟨fun q hq => ?_, fun z hfz => ?_⟩
        · rcases List.mem_append.mp hq with h1 | h2
          · exact hbvBinds q h1
          · exact harmBound q (List.mem_filter.mp h2).1
        · rw [resolveAlias_append_filter]
          cases hlb : binds.lookup z with
          | some fv =>
            have hzMem : z ∈ Δ.map Prod.fst := by
              rw [hdomB]; exact List.mem_map.mpr ⟨(z, fv), mem_of_lookup_eq_some hlb, rfl⟩
            obtain ⟨fv', hlb', hΔeq⟩ := hlookB z (by simp [hlb])
            rw [hlb, Option.some.injEq] at hlb'; subst hlb'
            rw [lookup_append_of_mem_poly hzMem, hΔeq]
          | none =>
            have hzNotB : z ∉ binds.map Prod.fst := not_mem_map_fst_of_lookup_none hlb
            have hzNotΔ : z ∉ Δ.map Prod.fst := by rw [hdomB]; exact hzNotB
            have hzNotP : z ∉ patBoundVars (.construct (.named enumTy []) nm pats) := by
              simp only [patBoundVars]; rw [← pitems.dom_eq]; exact hzNotΔ
            rw [lookup_append_of_not_mem_poly hzNotΔ]
            exact haArms.2 z (harmFree z hzNotP hfz)
termination_by fuel _ _ _ _ _ e _ _ _ _ _ => (fuel, sizeOf e)
decreasing_by
  all_goals try simp_wf
  all_goals try subst_vars
  all_goals omega

theorem hasTyList_simpExprList {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap)
      {ΓOrig ΓOpt : TyEnv} {xs : List Expr} {ts : List Lower.Ty},
      AliasTyInvList a ΓOrig ΓOpt xs →
      CtorTyInv c enums ΓOpt →
      CompactTyInv m ΓOpt →
      HasTyList (fnSigsOf fns) enums ΓOrig xs ts →
      HasTyList (fnSigsOf fns) enums ΓOpt (simpExprList fuel a c m xs) ts
  | _, _, _, _, _, _, _, _, _, _, _, .nil => by rw [simpExprList]; exact .nil
  | fuel, a, c, m, _, _, _, _, ha, hc, hm, .cons hd tl => by
    rw [simpExprList]
    exact .cons
      (hasTy_simpExpr hSigs fuel a c m
        ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVarList, Bool.or_eq_false_iff] at this; exact this.1,
         fun x hx => ha.2 x (by simp [hasFreeVarList, hx])⟩ hc hm hd)
      (hasTyList_simpExprList hSigs fuel a c m
        ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVarList, Bool.or_eq_false_iff] at this; exact this.2,
         fun x hx => ha.2 x (by simp [hasFreeVarList, hx])⟩ hc hm tl)
termination_by fuel _ _ _ _ _ xs _ _ _ _ _ => (fuel, sizeOf xs)

theorem hasTyArms_simpArms {fns : List Fn} {enums : List Aiur.Generic.EnumDecl}
    (hSigs : HasU32HelperSigs fns) :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap)
      {ΓOrig ΓOpt : TyEnv} {ts tb : Lower.Ty} {arms : List (Pat × Expr)},
      AliasTyInvArms a ΓOrig ΓOpt arms →
      CtorTyInv c enums ΓOpt →
      CompactTyInv m ΓOpt →
      HasTyArms (fnSigsOf fns) enums ΓOrig ts arms tb →
      HasTyArms (fnSigsOf fns) enums ΓOpt ts (simpArms fuel a c m arms) tb
  | _, _, _, _, _, _, _, _, _, _, _, _, .nil => by rw [simpArms]; exact .nil
  | fuel, a, c, m, ΓOrig, ΓOpt, _, _, (p, b) :: rest, ha, hc, hm, .cons hp hb tl => by
    have hno2 : ∀ q ∈ a, q.2 ∉ patBoundVars p ∧ hasBoundVar q.2 b = false := by
      intro q hq
      have h0 := ha.1 q hq
      simp only [hasBoundVarArms, Bool.or_eq_false_iff] at h0
      exact ⟨(fun hmem => by have := List.contains_iff_mem.mpr hmem; rw [this] at h0; cases h0.1.1), h0.1.2⟩
    have hfreeB : ∀ z, z ∉ patBoundVars p → hasFreeVar z b = true →
        ΓOrig.lookup z = ΓOpt.lookup (resolveAlias a z) :=
      fun z hnot hfz => ha.2 z (by simp [hasFreeVarArms, hnot, hfz])
    have haB := aliasTyInv_shadow (ctors := c) (compacts := m) hp.dom_eq hno2 hfreeB
    have hc0 := ctorTyInv_shadow (a := a) (m := m) hc hp.dom_eq
    have hm0 := compactTyInv_shadow (a := a) (c := c) hm hp.dom_eq
    have haRest : AliasTyInvArms a ΓOrig ΓOpt rest :=
      ⟨fun q hq => by have := ha.1 q hq; simp only [hasBoundVarArms, Bool.or_eq_false_iff] at this; exact this.2,
       fun z hz => ha.2 z (by simp [hasFreeVarArms, hz])⟩
    rw [simpArms]
    exact .cons hp (hasTy_simpExpr hSigs fuel _ _ _ haB hc0 hm0 hb)
      (hasTyArms_simpArms hSigs fuel a c m haRest hc hm tl)
termination_by fuel _ _ _ _ _ _ _ arms _ _ _ _ => (fuel, sizeOf arms)

end

/-! ### Part 8D: Runtime Invariants, `isPureCtorOrVar`, `selectArm_of_pickCtorArm`, & `evalExpr_simpExpr_backward` -/

section SimpExprEval

variable {F : Type} [Field F] [DecidableEq F]

def AliasLocInv (aliases : AliasMap) (locOrig locOpt : Environment F Nat) (e : Expr) : Prop :=
  (∀ q ∈ aliases, hasBoundVar q.2 e = false) ∧
  (∀ x, hasFreeVar x e = true →
    (locOrig.find? (·.1 == x)).map Prod.snd =
    (locOpt.find? (·.1 == resolveAlias aliases x)).map Prod.snd)

def AliasLocInvList (aliases : AliasMap) (locOrig locOpt : Environment F Nat) (xs : List Expr) : Prop :=
  (∀ q ∈ aliases, hasBoundVarList q.2 xs = false) ∧
  (∀ x, hasFreeVarList x xs = true →
    (locOrig.find? (·.1 == x)).map Prod.snd =
    (locOpt.find? (·.1 == resolveAlias aliases x)).map Prod.snd)

def AliasLocInvArms (aliases : AliasMap) (locOrig locOpt : Environment F Nat) (arms : List (Pat × Expr)) : Prop :=
  (∀ q ∈ aliases, hasBoundVarArms q.2 arms = false) ∧
  (∀ x, hasFreeVarArms x arms = true →
    (locOrig.find? (·.1 == x)).map Prod.snd =
    (locOpt.find? (·.1 == resolveAlias aliases x)).map Prod.snd)

def CtorLocInv (ctors : CtorMap) (locOpt : Environment F Nat) : Prop :=
  ∀ v en nm fvs, (v, (en, nm, fvs)) ∈ ctors →
    ∃ vs, locOpt.find? (·.1 == v) = some (v, .construct (qualifyName en) nm vs) ∧
      List.Forall₂ (fun fv val => locOpt.find? (·.1 == fv) = some (fv, val)) fvs vs

def CompactLocInv (compacts : AliasMap) (locOpt : Environment F Nat) : Prop :=
  ∀ t u, (t, u) ∈ compacts →
    ∃ n w, locOpt.find? (·.1 == u) = some (u, w) ∧ isU32Val n w ∧
      locOpt.find? (·.1 == t) = some (t, .field (n : F))

omit [Field F] [DecidableEq F] in
private theorem ctorLocInv_shadow {ctors : CtorMap} {locOpt bsEnv : Environment F Nat}
    {bs : List String} {a : AliasMap} {m : AliasMap}
    (hc : CtorLocInv ctors locOpt) (hdom : bsEnv.map Prod.fst = bs) :
    CtorLocInv (shadowMaps bs a ctors m).2.1 (bsEnv ++ locOpt) := by
  intro v en nm fvs hmem
  obtain ⟨hmemOrig, hfilt⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hfilt
  have hvNot : v ∉ bs := fun hm => by
    have := List.contains_iff_mem.mpr hm; rw [this] at hfilt; cases hfilt.1
  obtain ⟨vs, hvLoc, hall⟩ := hc v en nm fvs hmemOrig
  refine ⟨vs, by rw [find?_append_of_not_mem_poly (hdom ▸ hvNot)]; exact hvLoc, ?_⟩
  have hnotAll : ∀ fv ∈ fvs, fv ∉ bs := fun fv hfv hm => by
    have h1 := hfilt.2 fv hfv; have := List.contains_iff_mem.mpr hm; rw [this] at h1; cases h1
  clear hfilt hmem hmemOrig hvLoc hvNot hc
  induction hall with
  | nil => exact .nil
  | @cons fv val fvs1 vs1 hfv _ ih =>
    refine .cons ?_ (ih fun x hx => hnotAll x (List.mem_cons_of_mem _ hx))
    rw [find?_append_of_not_mem_poly (hdom ▸ hnotAll fv List.mem_cons_self)]; exact hfv

omit [DecidableEq F] in
private theorem compactLocInv_shadow {compacts : AliasMap} {locOpt bsEnv : Environment F Nat}
    {bs : List String} {a : AliasMap} {c : CtorMap}
    (hm : CompactLocInv compacts locOpt) (hdom : bsEnv.map Prod.fst = bs) :
    CompactLocInv (shadowMaps bs a c compacts).2.2 (bsEnv ++ locOpt) := by
  intro t u hmem
  obtain ⟨hmemOrig, hfilt⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfilt
  have htNot : t ∉ bs := fun h => by
    have := List.contains_iff_mem.mpr h; rw [this] at hfilt; cases hfilt.1
  have huNot : u ∉ bs := fun h => by
    have := List.contains_iff_mem.mpr h; rw [this] at hfilt; cases hfilt.2
  obtain ⟨n, w, huLoc, hw, htLoc⟩ := hm t u hmemOrig
  exact ⟨n, w, by rw [find?_append_of_not_mem_poly (hdom ▸ huNot)]; exact huLoc, hw,
    by rw [find?_append_of_not_mem_poly (hdom ▸ htNot)]; exact htLoc⟩

omit [Field F] [DecidableEq F] in
private theorem aliasLocInv_shadow {aliases : AliasMap} {ctors : CtorMap} {compacts : AliasMap}
    {locOrig locOpt bsEnv : Environment F Nat} {p : Pat} {b : Expr}
    (hdom : bsEnv.map Prod.fst = patBoundVars p)
    (hno2 : ∀ q ∈ aliases, q.2 ∉ patBoundVars p ∧ hasBoundVar q.2 b = false)
    (hfree : ∀ x, x ∉ patBoundVars p → hasFreeVar x b = true →
      (locOrig.find? (·.1 == x)).map Prod.snd = (locOpt.find? (·.1 == resolveAlias aliases x)).map Prod.snd) :
    AliasLocInv (shadowMaps (patBoundVars p) aliases ctors compacts).1 (bsEnv ++ locOrig) (bsEnv ++ locOpt) b := by
  refine ⟨fun q hq => (hno2 q (List.mem_filter.mp hq).1).2, fun x hfx => ?_⟩
  rw [resolveAlias_shadowMaps (patBoundVars p) aliases ctors compacts (fun q hq => (hno2 q hq).1)]
  by_cases hx : x ∈ patBoundVars p
  · simp only [hx, ↓reduceIte]
    rw [find?_append_of_mem_poly (hdom ▸ hx), find?_append_of_mem_poly (hdom ▸ hx)]
  · simp only [hx, ↓reduceIte]
    have hrNot : resolveAlias aliases x ∉ patBoundVars p := by
      unfold resolveAlias
      cases hl : aliases.lookup x with
      | none => exact hx
      | some y => exact (hno2 (x, y) (mem_of_lookup_eq_some hl)).1
    rw [find?_append_of_not_mem_poly (hdom ▸ hx), find?_append_of_not_mem_poly (hdom ▸ hrNot)]
    exact hfree x hx hfx

private theorem evalArgs_pureVarsOrLits {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} {ΓOpt : TyEnv} {locOpt : Environment F Nat} {h : Heap F}
    (henv : EnvOk enums h h.length ΓOpt locOpt) :
    ∀ {ys : List Expr} {ts : List Lower.Ty},
      (∀ y ∈ ys, (match y with | .var _ | .literal _ => true | _ => false) = true) →
      HasTyList (fnSigsOf fns) enums ΓOpt ys ts →
      ∃ vs, EvalArgs world [] locOpt (ys.map (qualifyExprF F)) h vs h
  | [], _, _, .nil => ⟨[], .nil⟩
  | y :: rest, ty :: ts', hall, .cons hy hrest => by
    have hyP := hall y List.mem_cons_self
    obtain ⟨vs, evRest⟩ := evalArgs_pureVarsOrLits henv (fun z hz => hall z (List.mem_cons_of_mem _ hz)) hrest
    cases y with
    | var u =>
      cases hy with | var hΓu =>
      obtain ⟨v, hfound, _⟩ := henv u ty hΓu
      exact ⟨v :: vs, .cons (by rw [qualifyExprF_var]; exact .var hfound) evRest⟩
    | literal n =>
      exact ⟨.field (n : F) :: vs, .cons (by rw [qualifyExprF_literal]; exact .literal) evRest⟩
    | _ => simp at hyP

/-- Constructive evaluation for any pure expression accepted by `isPureCtorOrVar`! -/
theorem evalExpr_isPureCtorOrVar {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world) {ΓOpt : TyEnv} {locOpt : Environment F Nat}
    {x : Expr} {tx : Lower.Ty} (h : Heap F)
    (hpure : isPureCtorOrVar x = true)
    (hty : HasTy (fnSigsOf fns) enums ΓOpt x tx)
    (henv : EnvOk enums h h.length ΓOpt locOpt) :
    ∃ v, EvalExpr world [] locOpt (qualifyExprF F x) h v h := by
  cases x with
  | var u =>
    cases hty with | var hΓu =>
    obtain ⟨v, hfound, _⟩ := henv u tx hΓu
    exact ⟨v, by rw [qualifyExprF_var]; exact .var hfound⟩
  | literal n =>
    exact ⟨.field (n : F), by rw [qualifyExprF_literal]; exact .literal⟩
  | construct en targs nm xs =>
    cases hty with | construct _ _ _ _ _ items =>
    simp only [isPureCtorOrVar, List.all_eq_true] at hpure
    obtain ⟨vs, evArgs⟩ := evalArgs_pureVarsOrLits henv hpure items
    refine ⟨.construct (qualifyName en) nm vs, ?_⟩
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
    rw [map_qualifyExprF]
    exact .construct evArgs
  | call nm targs xs =>
    simp only [isPureCtorOrVar] at hpure
    cases hmc : matchCompactU32 (.call nm targs xs) with
    | none => rw [hmc] at hpure; cases hpure
    | some inner =>
      cases inner with
      | var u =>
        obtain ⟨_, huTy⟩ := hasTy_compactU32_inv hmc hty
        cases huTy with | var hΓu =>
        obtain ⟨w, hfound, hokW⟩ := henv u u32Ty hΓu
        obtain ⟨n, hn⟩ := (ValOk_u32 ..).mp hokW
        refine ⟨.field (n : F), ?_⟩
        rw [matchCompactU32_inv hmc, qualifyExprF_call]
        simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_call, qualifyExprF_var,
          show qualifyName "UInt32::compact_field" = "UInt32::compact_field" from rfl,
          show qualifyName "UInt32::compact" = "UInt32::compact" from rfl]
        refine .call (.cons (.call (.cons (.var hfound) .nil)
            (by simpa [instanceName, Instance.symbol] using spec.compact_mk n w h hn)) .nil)
          (by simpa [instanceName, Instance.symbol] using spec.compact_field_mk (.field (n : F)) h)
      | _ => rw [hmc] at hpure; cases hpure
  | global _ _ | control _ _ | tuple _ | array _ | constructAs _ _ _ _ | record _ _
  | update _ _ | builtin _ _ | «repeat» _ _ | index _ _ | slice _ _ _ | member _ _
  | project _ _ | store _ | load _ | hint _ _ _ | neg _ | binary _ _ _ | letValue _ _ _
  | matchValue _ _ => simp [isPureCtorOrVar, matchCompactU32] at hpure

private theorem evalArgs_map_var_inv {world : World F} {loc : Environment F Nat} :
    ∀ {fvs : List String} {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs world [] loc ((fvs.map Aiur.Generic.Expr.var).map (qualifyExprF F)) h vs h' →
      h' = h ∧ List.Forall₂ (fun fv val => loc.find? (·.1 == fv) = some (fv, val)) fvs vs
  | [], _, _, _, ev => by cases ev; exact ⟨rfl, .nil⟩
  | fv :: fvs, _, _, _, ev => by
    simp only [List.map_cons, qualifyExprF_var] at ev
    cases ev with | cons evH evT =>
      cases evH with | var hl =>
        obtain ⟨rfl, hall⟩ := evalArgs_map_var_inv evT
        exact ⟨rfl, .cons hl hall⟩

private theorem evalArgs_map_var_mk {world : World F} {loc : Environment F Nat} {h : Heap F} :
    ∀ {fvs : List String} {vs : List (SourceValue F)},
      List.Forall₂ (fun fv val => loc.find? (·.1 == fv) = some (fv, val)) fvs vs →
      EvalArgs world [] loc ((fvs.map Aiur.Generic.Expr.var).map (qualifyExprF F)) h vs h
  | _, _, .nil => .nil
  | _, _, .cons hl tl => by
    simp only [List.map_cons, qualifyExprF_var]
    exact .cons (.var hl) (evalArgs_map_var_mk tl)

private theorem matchListWith_matchCtorPats {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {h : Heap F} {ΓOpt : TyEnv} {locOpt : Environment F Nat} :
    ∀ {pats : List Pat} {fts : List Lower.Ty} {Δ : TyEnv} {fvs : List String}
      {vs : List (SourceValue F)} {binds : AliasMap},
      PatListHasTy enums pats fts Δ →
      matchCtorPats pats fvs = some binds →
      List.Forall₂ (fun fv val => locOpt.find? (·.1 == fv) = some (fv, val)) fvs vs →
      List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs fts →
      ∃ bs, matchListWith (fun p v => world.matchPattern [] h p v) (pats.map (qualifyPatF F)) vs =
          .ok (some bs) ∧
        bs.map Prod.fst = binds.map Prod.fst ∧
        Δ.map Prod.fst = binds.map Prod.fst ∧
        (∀ v fv, binds.lookup v = some fv →
          (bs.find? (·.1 == v)).map Prod.snd = (locOpt.find? (·.1 == fv)).map Prod.snd ∧
          Δ.lookup v = ΓOpt.lookup fv)
  | [], _, _, [], _, _, .nil, hm, .nil, .nil => by
    simp only [matchCtorPats, Option.some.injEq] at hm; subst hm
    exact ⟨[], by simp [matchListWith, pure, Except.pure], rfl, rfl, fun _ _ h => by cases h⟩
  | .bind v :: ps, ft :: fts, _, fv :: fvs, val :: vs, binds, .cons .bind tl, hm, .cons hloc hlocs, .cons hty htys => by
    simp only [matchCtorPats] at hm
    cases hr : matchCtorPats ps fvs with
    | none => rw [hr] at hm; cases hm
    | some bs0 =>
      rw [hr] at hm; simp only [Option.map_some, Option.some.injEq] at hm; subst hm
      obtain ⟨bs, hml, hdomBs, hdomΔ, hlook⟩ := matchListWith_matchCtorPats (world := world) (h := h) tl hr hlocs htys
      refine ⟨(v, val) :: bs, ?_, by simp [hdomBs], by simp [hdomΔ], fun x fx hlk => ?_⟩
      · simp only [List.map_cons, matchListWith, matchPattern_bind_ok, bind, Except.bind, hml,
          pure, Except.pure, List.cons_append, List.nil_append]
      · by_cases hxv : x = v
        · subst hxv
          simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hlk; subst hlk
          exact ⟨by simp [hloc], by simp [hty]⟩
        · simp only [List.lookup, beq_false_of_ne hxv] at hlk ⊢
          obtain ⟨hl1, hl2⟩ := hlook x fx hlk
          exact ⟨by simp [beq_false_of_ne (Ne.symm hxv), hl1],
            by simp only [List.cons_append, List.nil_append, List.lookup, beq_false_of_ne hxv]; exact hl2⟩
  | .wildcard :: ps, ft :: fts, _, fv :: fvs, val :: vs, binds, .cons .wildcard tl, hm, .cons _ hlocs, .cons _ htys => by
    simp only [matchCtorPats] at hm
    obtain ⟨bs, hml, hdomBs, hdomΔ, hlook⟩ := matchListWith_matchCtorPats (world := world) (h := h) tl hm hlocs htys
    refine ⟨bs, ?_, hdomBs, by simpa using hdomΔ, hlook⟩
    have hwild : world.matchPattern [] h (qualifyPatF F .wildcard) val = .ok (some []) := by
      simp [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern, matchPatternWith, pure, Except.pure]
    simp only [List.map_cons, matchListWith, hwild, bind, Except.bind, hml, pure, Except.pure, List.nil_append]
  | .literal _ :: _, _, _, _, _, _, _, hm, _, _ | .tuple _ :: _, _, _, _, _, _, _, hm, _, _
  | .array _ :: _, _, _, _, _, _, _, hm, _, _ | .construct _ _ _ :: _, _, _, _, _, _, _, hm, _, _
  | .global _ _ :: _, _, _, _, _, _, _, hm, _, _ | .load _ :: _, _, _, _, _, _, _, hm, _, _
  | .orElse _ _ _ :: _, _, _, _, _, _, _, hm, _, _ | .repeat _ _ :: _, _, _, _, _, _, _, hm, _, _
  | .record _ _ :: _, _, _, _, _, _, _, hm, _, _ | .constructAs _ _ _ _ :: _, _, _, _, _, _, _, hm, _, _ => by
    simp [matchCtorPats] at hm

private theorem selectArm_of_pickCtorArm {world : World F} {fns : List Fn}
    {enums : List Aiur.Generic.EnumDecl} {h : Heap F}
    {ΓOrig ΓOpt : TyEnv} {locOpt : Environment F Nat}
    {enumTy nm : String} {fvs : List String} {vs : List (SourceValue F)} {fts : List Lower.Ty}
    {tb : Lower.Ty}
    (hctor : findCtorFields enums enumTy nm = some fts)
    (hlocs : List.Forall₂ (fun fv val => locOpt.find? (·.1 == fv) = some (fv, val)) fvs vs)
    (htys : List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs fts) :
    ∀ {arms : List (Pat × Expr)} {binds : AliasMap} {armBody : Expr},
      HasTyArms (fnSigsOf fns) enums ΓOrig (.named enumTy []) arms tb →
      pickCtorArm enumTy nm fvs arms = some (binds, armBody) →
      ∃ p bs Δ, (p, armBody) ∈ arms ∧
        PatHasTy enums p (.named enumTy []) Δ ∧
        HasTy (fnSigsOf fns) enums (Δ ++ ΓOrig) armBody tb ∧
        SourceSemantics.selectArm world [] h (.construct (qualifyName enumTy) nm vs)
            (arms.map fun arm => (qualifyPatF F arm.1, qualifyExprF F arm.2)) =
          .ok (some (bs, qualifyExprF F armBody)) ∧
        bs.map Prod.fst = binds.map Prod.fst ∧
        Δ.map Prod.fst = binds.map Prod.fst ∧
        (∀ v fv, binds.lookup v = some fv →
          (bs.find? (·.1 == v)).map Prod.snd = (locOpt.find? (·.1 == fv)).map Prod.snd ∧
          Δ.lookup v = ΓOpt.lookup fv)
  | [], _, _, .nil, hp => by simp [pickCtorArm] at hp
  | (p, b) :: rest, binds, armBody, .cons (Δ := Δ) hpPat hb tl, hpick => by
    have hlenVs : fvs.length = vs.length := hlocs.length_eq
    cases hpPat with
    | wildcard =>
      simp only [pickCtorArm, Option.some.injEq, Prod.mk.injEq] at hpick
      obtain ⟨rfl, rfl⟩ := hpick
      refine ⟨.wildcard, [], [], List.mem_cons_self, .wildcard, hb, ?_, rfl, rfl, fun _ _ h => by cases h⟩
      simp [SourceSemantics.selectArm, qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map,
        World.matchPattern, matchPatternWith, bind, Except.bind, pure, Except.pure]
    | bind => simp [pickCtorArm] at hpick
    | @construct _ ctor' pats fts' _ hne4 hctor' pitems =>
      simp only [pickCtorArm, beq_self_eq_true, Bool.true_and] at hpick
      by_cases hcond : (ctor' == nm && pats.length == fvs.length) = true
      · simp only [hcond, ↓reduceIte] at hpick
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨rfl, hplen⟩ := hcond
        cases hmp : matchCtorPats pats fvs with
        | none => simp [hmp] at hpick
        | some bs0 =>
          rw [hmp] at hpick; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpick
          obtain ⟨rfl, rfl⟩ := hpick
          rw [hctor] at hctor'; simp only [Option.some.injEq] at hctor'; subst hctor'
          obtain ⟨bs, hml, hdomBs, hdomΔ, hlook⟩ := matchListWith_matchCtorPats (world := world) (h := h) pitems hmp hlocs htys
          refine ⟨_, bs, Δ, List.mem_cons_self, .construct hne4 hctor pitems, hb, ?_, hdomBs, hdomΔ, hlook⟩
          have hmatch : world.matchPattern [] h (qualifyPatF F (.construct (.named enumTy []) ctor' pats))
              (.construct (qualifyName enumTy) ctor' vs) = .ok (some bs) := by
            simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern]
            rw [matchPatternWith]
            have hcn : constructorName [] (.named (qualifyName enumTy) []) = qualifyName enumTy := by
              simp [constructorName, Aiur.Generic.Ty.toCore, Instance.symbol]
            have hlenEq : pats.length = vs.length := hplen.trans hlenVs
            simp only [qualifyTy, List.map_nil, hcn, List.length_map, hlenEq, bne_self_eq_false,
              Bool.or_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
              pure, Except.pure, matchListWith_attach, map_qualifyPatF_eq]
            exact hml
          simp [SourceSemantics.selectArm, hmatch, bind, Except.bind, pure, Except.pure]
      · have hcondF : (ctor' == nm && pats.length == fvs.length) = false := Bool.eq_false_iff.mpr hcond
        rw [hcondF] at hpick; simp only [Bool.false_eq_true, ↓reduceIte] at hpick
        have hnone : world.matchPattern [] h (qualifyPatF F (.construct (.named enumTy []) ctor' pats))
            (.construct (qualifyName enumTy) nm vs) = .ok none := by
          simp only [qualifyPatF, qualifyPat, Aiur.Generic.Pattern.map, World.matchPattern]
          rw [matchPatternWith]
          have hcn : constructorName [] (.named (qualifyName enumTy) []) = qualifyName enumTy := by
            simp [constructorName, Aiur.Generic.Ty.toCore, Instance.symbol]
          have hne : (qualifyName enumTy != qualifyName enumTy || nm != ctor' ||
              (List.map (Aiur.Generic.Pattern.map (Nat.cast : Nat → F)) (List.map qualifyPat pats)).length != vs.length) = true := by
            simp only [List.length_map, ← hlenVs]
            by_cases hcn' : ctor' = nm
            · subst hcn'
              have hneLen : pats.length ≠ fvs.length := fun heq => hcond (by simp [heq])
              simp [bne_iff_ne, hneLen]
            · simp [bne_iff_ne, Ne.symm hcn']
          simp only [qualifyTy, List.map_nil, hcn, hne, ↓reduceIte, pure, Except.pure]
        obtain ⟨p0, bs, Δ0, hmem, hp0, hb0, hsel, hdomBs, hdomΔ, hlook⟩ :=
          selectArm_of_pickCtorArm (world := world) (h := h) hctor hlocs htys tl hpick
        refine ⟨p0, bs, Δ0, List.mem_cons_of_mem _ hmem, hp0, hb0, ?_, hdomBs, hdomΔ, hlook⟩
        simp [SourceSemantics.selectArm, hnone, bind, Except.bind, hsel]

private theorem evalExpr_letBind_post_inv {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world)
    {ΓOpt : TyEnv} {locOpt : Environment F Nat}
    {v : String} {x' b' res : Expr} {tx tb : Lower.Ty} {h h' : Heap F} {r : SourceValue F}
    (hres : res = .letValue (.bind v) x' b' ∨ (res = x' ∧ b' = .var v) ∨
      (res = b' ∧ isPureCtorOrVar x' = true ∧ hasFreeVar v b' = false))
    (hx' : HasTy (fnSigsOf fns) enums ΓOpt x' tx)
    (hb' : HasTy (fnSigsOf fns) enums ((v, tx) :: ΓOpt) b' tb)
    (henv : EnvOk enums h h.length ΓOpt locOpt)
    (ev : EvalExpr world [] locOpt (qualifyExprF F res) h r h') :
    ∃ vx hm, EvalExpr world [] locOpt (qualifyExprF F x') h vx hm ∧
      EvalExpr world [] ((v, vx) :: locOpt) (qualifyExprF F b') hm r h' := by
  rcases hres with rfl | ⟨rfl, rfl⟩ | ⟨hresEq, hpure, hnotFree⟩
  · exact evalExpr_let_bind_qual_inv ev
  · exact ⟨r, h', ev, by rw [qualifyExprF_var]; exact .var (by simp)⟩
  · rw [hresEq] at ev
    obtain ⟨vx, evX'⟩ := evalExpr_isPureCtorOrVar spec h hpure hx' henv
    have evB' : EvalExpr world [] ((v, vx) :: locOpt) (qualifyExprF F b') h r h' := by
      refine evalExpr_localsAgree hb'.isClean (fun z hz => ?_) ev
      have hne : z ≠ v := by intro heq; subst heq; rw [hnotFree] at hz; cases hz
      simp [beq_false_of_ne (Ne.symm hne)]
    exact ⟨vx, h, evX', evB'⟩

private theorem evalExpr_compactU32_inv {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} (spec : U32WorldSpec world)
    {ΓOpt : TyEnv} {locOpt : Environment F Nat}
    {x' : Expr} {u : String} {tx : Lower.Ty} {h hm : Heap F} {vx : SourceValue F}
    (hmc : matchCompactU32 x' = some (.var u))
    (hx' : HasTy (fnSigsOf fns) enums ΓOpt x' tx)
    (henv : EnvOk enums h h.length ΓOpt locOpt)
    (evX' : EvalExpr world [] locOpt (qualifyExprF F x') h vx hm) :
    ∃ n w, locOpt.find? (·.1 == u) = some (u, w) ∧ isU32Val n w ∧ vx = .field (n : F) := by
  obtain ⟨_, huTy⟩ := hasTy_compactU32_inv hmc hx'
  cases huTy with | var hΓu =>
  rw [matchCompactU32_inv hmc, qualifyExprF_call] at evX'
  simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_call, qualifyExprF_var,
    show qualifyName "UInt32::compact_field" = "UInt32::compact_field" from rfl,
    show qualifyName "UInt32::compact" = "UInt32::compact" from rfl] at evX'
  obtain ⟨vc, hc1, evCmp, hfnCf⟩ := evalExpr_call1_inv evX'
  obtain ⟨w, hw1, evU, hfnCmp⟩ := evalExpr_call1_inv evCmp
  cases evU with | var hfound =>
  obtain ⟨w0, hfound0, hokW⟩ := henv u u32Ty hΓu
  rw [hfound0, Option.some.injEq, Prod.mk.injEq] at hfound
  obtain ⟨_, rfl⟩ := hfound
  obtain ⟨n, hn⟩ := (ValOk_u32 ..).mp hokW
  obtain ⟨rfl, rfl⟩ := spec.tg.compact n w0 _ vc hc1 hn hfnCmp
  obtain ⟨rfl, _⟩ := spec.tg.compact_field (.field (n : F)) _ vx hm hfnCf
  exact ⟨n, w0, hfound0, hn, rfl⟩

private theorem simpArms_eq_map (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap)
    (arms : List (Pat × Expr)) :
    simpArms fuel a c m arms =
      arms.map fun arm =>
        let (a0, c0, m0) := shadowMaps (patBoundVars arm.1) a c m
        (arm.1, simpExpr fuel a0 c0 m0 arm.2) := by
  induction arms with
  | nil => rw [simpArms]; rfl
  | cons hd tl ih => rcases hd with ⟨p, b⟩; simp [simpArms, ih]

mutual

/-- **Stage 6 (`simpExpr`) Backward Soundness:**
Covers copy propagation, known-constructor `matchValue` folding, dead pure `let` elimination,
eta-reduction (`let v := x; v → x`), and `u32_of_field`/`UInt32::from_field` cancellation of
`UInt32::compact_field (UInt32::compact x)`! -/
theorem evalExpr_simpExpr_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap)
      {ΓOrig ΓOpt : TyEnv} {locOrig locOpt : Environment F Nat}
      {e : Expr} {t : Lower.Ty} {h h' : Heap F} {r : SourceValue F},
      AliasTyInv a ΓOrig ΓOpt e →
      AliasLocInv a locOrig locOpt e →
      CtorTyInv c enums ΓOpt →
      CtorLocInv c locOpt →
      CompactTyInv m ΓOpt →
      CompactLocInv m locOpt →
      HasTy (fnSigsOf fns) enums ΓOrig e t →
      EnvOk enums h h.length ΓOpt locOpt →
      EvalExpr world [] locOpt (qualifyExprF F (simpExpr fuel a c m e)) h r h' →
      EvalExpr world [] locOrig (qualifyExprF F e) h r h'
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .literal, _, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev; exact .literal
  | _, a, _, _, _, _, locOrig, locOpt, .var x, _, _, _, r, _, hal, _, _, _, _, .var _, _, ev => by
    simp only [simpExpr, qualifyExprF_var] at ev
    rw [qualifyExprF_var]
    cases ev with | var hl =>
      have heq := hal.2 x (by simp [hasFreeVar])
      rw [hl] at heq
      cases ho : locOrig.find? (·.1 == x) with
      | none => rw [ho] at heq; cases heq
      | some kv =>
        rw [ho] at heq; simp only [Option.map_some, Option.some.injEq] at heq
        rcases kv with ⟨k, v⟩; dsimp only at heq; subst heq
        have hk : k = x := by simpa [beq_iff_eq] using List.find?_some ho
        subst hk; exact .var ho
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .tuple items, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | tuple evs =>
      exact .tuple (evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml items henv evs)
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .array _ items, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | array evs =>
      exact .array (evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml items henv evs)
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .repeat hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | «repeat» item =>
      exact .repeat (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item)
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .index hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | index item hp =>
      exact .index (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item) hp
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .project hx _, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | project item hp =>
      exact .project (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item) hp
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .slice _ hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | slice item hs =>
      exact .slice (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item) hs
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .construct _ _ _ _ _ items, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | construct evs =>
      exact .construct (evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml items henv evs)
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .builtin items, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    rw [map_qualifyExprF] at ev ⊢
    cases ev with | builtin evs ha =>
      exact .builtin (evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml items henv evs) ha
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .store hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | store item =>
      exact .store (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item)
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .load hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | load item hl =>
      exact .load (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item) hl
  | fuel, a, c, m, _, _, _, _, .hint _ x _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .hint _ hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | hint item ht =>
      exact .hint (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m (e := x) hat hal hct hcl hmt hml hx henv item) ht
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .neg hx, henv, ev => by
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | neg item hop =>
      exact .neg (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml hx henv item) hop
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .binary hl hr, henv, ev => by
    have hatL : AliasTyInv a _ _ _ :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1,
       fun x hx => hat.2 x (by simp [hasFreeVar, hx])⟩
    have halL : AliasLocInv a _ _ _ :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1,
       fun x hx => hal.2 x (by simp [hasFreeVar, hx])⟩
    have hatR : AliasTyInv a _ _ _ :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.2,
       fun x hx => hat.2 x (by simp [hasFreeVar, hx])⟩
    have halR : AliasLocInv a _ _ _ :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.2,
       fun x hx => hal.2 x (by simp [hasFreeVar, hx])⟩
    simp only [simpExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with | binary evL evR hop =>
      have evL' := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hatL halL hct hcl hmt hml hl henv evL
      have hext := evL'.heap_extends
      have evR' := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hatR halR hct hcl hmt hml hr (henv.mono hext hext.length_le) evR
      exact .binary evL' evR' hop
  | fuel, a, c, m, _, _, _, locOpt, .call nm (some []) xs, t, h, h', r, hat, hal, hct, hcl, hmt, hml,
      .call hsig items, henv, ev => by
    rcases simpExpr_call_cases fuel a c m nm (some []) xs with
      hres | ⟨hnm, _, ⟨x0, tvar, u, hxs, hx0, hlk, hres⟩ | ⟨x0, arg, inner, hxs, hx0, hmc, hres⟩⟩
    · rw [hres, qualifyExprF_call] at ev
      rw [qualifyExprF_call]
      cases ev with | call evs hfn =>
        exact .call (evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
          fuel a c m hat hal hct hcl hmt hml items henv evs) hfn
    · rw [hres, qualifyExprF_var] at ev
      cases ev with | var huFound =>
      obtain ⟨n, w, huLoc, hw, htLoc⟩ := hml tvar u (mem_of_lookup_eq_some hlk)
      rw [huLoc, Option.some.injEq, Prod.mk.injEq] at huFound
      obtain ⟨_, rfl⟩ := huFound
      have evArg' : EvalExpr world [] locOpt (qualifyExprF F (simpExpr fuel a c m x0)) h (.field (n : F)) h := by
        rw [hx0, qualifyExprF_var]; exact .var htLoc
      have evArgs' : EvalArgs world [] locOpt ((simpExprList fuel a c m xs).map (qualifyExprF F)) h [.field (n : F)] h := by
        rw [hxs, simpExprList, simpExprList, List.map_cons, List.map_nil]
        exact .cons evArg' .nil
      have evArgs := evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml items henv evArgs'
      rw [qualifyExprF_call]
      simp only [Option.map_some, List.map_nil]
      rcases hnm with rfl | rfl
      · refine .call evArgs ?_
        rw [show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl]
        have hlt := isU32Val_lt hw
        simpa [instanceName, Instance.symbol] using
          spec.u32_of_field_mk n w h (lt_trans hlt (by unfold U32.base natLimit; omega)) (by rwa [Nat.mod_eq_of_lt hlt])
      · refine .call evArgs ?_
        rw [show qualifyName "UInt32::from_field" = "UInt32::from_field" from rfl]
        simpa [instanceName, Instance.symbol] using spec.from_field_mk n w h hw
    · rw [hres] at ev
      have hxsTy := hasTyList_simpExprList hSigs fuel a c m hat hct hmt items
      rw [hxs, simpExprList] at hxsTy
      cases hxsTy with | cons hargTy _ =>
      rw [hx0] at hargTy
      obtain ⟨_, hinnerTy⟩ := hasTy_compactU32_inv hmc hargTy
      have hokR := evalExpr_valOk hnd hHas hProv hLib spec hWT hinnerTy henv ev
      obtain ⟨n, hrU32⟩ := (ValOk_u32 ..).mp hokR
      have evArg' : EvalExpr world [] locOpt (qualifyExprF F (simpExpr fuel a c m x0)) h (.field (n : F)) h' := by
        rw [hx0, matchCompactU32_inv hmc, qualifyExprF_call]
        simp only [Option.map_some, List.map_nil, List.map_cons, qualifyExprF_call,
          show qualifyName "UInt32::compact_field" = "UInt32::compact_field" from rfl,
          show qualifyName "UInt32::compact" = "UInt32::compact" from rfl]
        refine .call (.cons (.call (.cons ev .nil)
            (by simpa [instanceName, Instance.symbol] using spec.compact_mk n r h' hrU32)) .nil)
          (by simpa [instanceName, Instance.symbol] using spec.compact_field_mk (.field (n : F)) h')
      have evArgs' : EvalArgs world [] locOpt ((simpExprList fuel a c m xs).map (qualifyExprF F)) h [.field (n : F)] h' := by
        rw [hxs, simpExprList, simpExprList, List.map_cons, List.map_nil]
        exact .cons evArg' .nil
      have evArgs := evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hat hal hct hcl hmt hml items henv evArgs'
      rw [qualifyExprF_call]
      simp only [Option.map_some, List.map_nil]
      rcases hnm with rfl | rfl
      · refine .call evArgs ?_
        rw [show qualifyName "u32_of_field" = qualified "u32_of_field" from rfl]
        have hlt := isU32Val_lt hrU32
        simpa [instanceName, Instance.symbol] using
          spec.u32_of_field_mk n r h' (lt_trans hlt (by unfold U32.base natLimit; omega)) (by rwa [Nat.mod_eq_of_lt hlt])
      · refine .call evArgs ?_
        rw [show qualifyName "UInt32::from_field" = "UInt32::from_field" from rfl]
        simpa [instanceName, Instance.symbol] using spec.from_field_mk n r h' hrU32
  | fuel, a, c, m, ΓOrig, ΓOpt, locOrig, locOpt, .letValue p x b, tb, h, h', r,
      hat, hal, hct, hcl, hmt, hml, .letValue (tx := tx) (Δ := Δ) hx hp hb, henv, ev => by
    have hatX : AliasTyInv a ΓOrig ΓOpt x :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1.2,
       fun z hz => hat.2 z (by simp [hasFreeVar, hz])⟩
    have halX : AliasLocInv a locOrig locOpt x :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1.2,
       fun z hz => hal.2 z (by simp [hasFreeVar, hz])⟩
    have hx' := hasTy_simpExpr hSigs fuel a c m hatX hct hmt hx
    have hno2 : ∀ q ∈ a, q.2 ∉ patBoundVars p ∧ hasBoundVar q.2 b = false := by
      intro q hq
      have h0 := hat.1 q hq
      simp only [hasBoundVar, Bool.or_eq_false_iff] at h0
      exact ⟨(fun hmem => by have := List.contains_iff_mem.mpr hmem; rw [this] at h0; cases h0.1.1), h0.2⟩
    have hfreeBTy : ∀ z, z ∉ patBoundVars p → hasFreeVar z b = true →
        ΓOrig.lookup z = ΓOpt.lookup (resolveAlias a z) :=
      fun z hnot hfz => hat.2 z (by simp [hasFreeVar, hnot, hfz])
    have hfreeBLoc : ∀ z, z ∉ patBoundVars p → hasFreeVar z b = true →
        (locOrig.find? (·.1 == z)).map Prod.snd = (locOpt.find? (·.1 == resolveAlias a z)).map Prod.snd :=
      fun z hnot hfz => hal.2 z (by simp [hasFreeVar, hnot, hfz])
    have hatB0 := aliasTyInv_shadow (ctors := c) (compacts := m) hp.dom_eq hno2 hfreeBTy
    have hct0 := ctorTyInv_shadow (a := a) (m := m) hct hp.dom_eq
    have hmt0 := compactTyInv_shadow (a := a) (c := c) hmt hp.dom_eq
    cases p with
    | bind v =>
      cases hp
      rcases simpExpr_letValue_bind_cases fuel a c m v x b with
        ⟨y, hy, hbvY, hres⟩ | ⟨c1, m1, hc1, hm1, hres⟩
      · rw [hres] at ev
        rw [hy] at hx'
        cases hx' with | var hΓy =>
        obtain ⟨vy, hyLoc, _⟩ := henv y tx hΓy
        have evX' : EvalExpr world [] locOpt (qualifyExprF F (simpExpr fuel a c m x)) h vy h := by
          rw [hy, qualifyExprF_var]; exact .var hyLoc
        have evX := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
          fuel a c m hatX halX hct hcl hmt hml hx henv evX'
        have hatB1 : AliasTyInv ((v, y) :: a.filter fun q => q.1 != v) ((v, tx) :: ΓOrig) ΓOpt b := by
          refine ⟨fun q hq => ?_, fun z hfz => ?_⟩
          · rcases List.mem_cons.mp hq with rfl | htl
            · exact hbvY
            · exact (hno2 q (List.mem_filter.mp htl).1).2
          · rw [resolveAlias_cons_filter]
            by_cases hzv : z = v
            · subst hzv; simp [hΓy]
            · simp only [hzv, ↓reduceIte, List.lookup, beq_false_of_ne hzv]
              exact hfreeBTy z (by simp [patBoundVars, hzv]) hfz
        have halB1 : AliasLocInv ((v, y) :: a.filter fun q => q.1 != v) ((v, vy) :: locOrig) locOpt b := by
          refine ⟨fun q hq => ?_, fun z hfz => ?_⟩
          · rcases List.mem_cons.mp hq with rfl | htl
            · exact hbvY
            · exact (hno2 q (List.mem_filter.mp htl).1).2
          · rw [resolveAlias_cons_filter]
            by_cases hzv : z = v
            · subst hzv; simp [hyLoc]
            · simp only [hzv, ↓reduceIte, List.find?_cons, beq_false_of_ne (Ne.symm hzv)]
              exact hfreeBLoc z (by simp [patBoundVars, hzv]) hfz
        have evB := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
          fuel _ c m hatB1 halB1 hct hcl hmt hml hb henv ev
        rw [qualifyExprF_letValue]
        exact .letValue evX (matchPattern_bind_ok v vy) evB
      · have hct1 : CtorTyInv c1 enums ((v, tx) :: ΓOpt) := by
          rcases hc1 with rfl | ⟨ty, nm, args, fvs, hxeq, hav, hvNot, rfl⟩
          · exact hct0
          · intro w en' nm' fvs' hmem
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, hinfo⟩ := Prod.mk.inj heq
              obtain ⟨rfl, rfl, rfl⟩ := hinfo
              rw [hxeq, allVarNames_inv hav] at hx'
              cases hx' with | construct _ _ _ _ hctor items =>
              refine ⟨by simp [List.lookup], _, hctor, ?_⟩
              have hall := hasTyList_map_var_inv items
              clear items hxeq hav hres hmem heq hctor
              induction hall with
              | nil => exact .nil
              | @cons fv ft fvs1 fts1 hfv _ ih =>
                simp only [List.mem_cons, not_or] at hvNot
                exact .cons (by simp [List.lookup, beq_false_of_ne (Ne.symm hvNot.1), hfv]) (ih hvNot.2)
            · exact hct0 w en' nm' fvs' htl
        have hmt1 : CompactTyInv m1 ((v, tx) :: ΓOpt) := by
          rcases hm1 with rfl | ⟨u, hmc, huv, rfl⟩
          · exact hmt0
          · intro tvar uvar hmem
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
              obtain ⟨_, huTy⟩ := hasTy_compactU32_inv hmc hx'
              cases huTy with | var hΓu =>
              simp [List.lookup, beq_false_of_ne huv, hΓu]
            · exact hmt0 tvar uvar htl
        have hb' := hasTy_simpExpr hSigs fuel _ c1 m1 hatB0 hct1 hmt1 hb
        obtain ⟨vx, hmHeap, evX', evB'⟩ := evalExpr_letBind_post_inv spec hres hx' hb' henv ev
        have hokVx := evalExpr_valOk hnd hHas hProv hLib spec hWT hx' henv evX'
        have hext := evX'.heap_extends
        have henvB : EnvOk enums hmHeap hmHeap.length ((v, tx) :: ΓOpt) ((v, vx) :: locOpt) :=
          envOk_append (.cons ⟨rfl, hokVx⟩ .nil) (henv.mono hext hext.length_le)
        have evX := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
          fuel a c m hatX halX hct hcl hmt hml hx henv evX'
        have halB0 := aliasLocInv_shadow (ctors := c) (compacts := m) (bsEnv := [(v, vx)]) (p := .bind v)
          rfl hno2 hfreeBLoc
        have hcl0 := ctorLocInv_shadow (a := a) (m := m) (bsEnv := [(v, vx)]) hcl rfl
        have hml0 := compactLocInv_shadow (a := a) (c := c) (bsEnv := [(v, vx)]) hml rfl
        have hcl1 : CtorLocInv c1 ((v, vx) :: locOpt) := by
          rcases hc1 with rfl | ⟨ty, nm, args, fvs, hxeq, hav, hvNot, rfl⟩
          · exact hcl0
          · intro w en' nm' fvs' hmem
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, hinfo⟩ := Prod.mk.inj heq
              obtain ⟨rfl, rfl, rfl⟩ := hinfo
              rw [hxeq, allVarNames_inv hav] at evX'
              simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evX'
              rw [map_qualifyExprF] at evX'
              cases evX' with | construct evArgs =>
                obtain ⟨_, hall⟩ := evalArgs_map_var_inv evArgs
                refine ⟨_, by simp [instanceName, Instance.symbol]; rfl, ?_⟩
                have go : ∀ {l1 : List String} {l2 : List (SourceValue F)} {v0 : SourceValue F},
                    w ∉ l1 →
                    List.Forall₂ (fun fv val => locOpt.find? (·.1 == fv) = some (fv, val)) l1 l2 →
                    List.Forall₂ (fun fv val => ((w, v0) :: locOpt).find? (·.1 == fv) = some (fv, val)) l1 l2 := by
                  intro l1 l2 v0 hnot hl
                  induction hl with
                  | nil => exact .nil
                  | @cons fv val fvs1 vs1 hfv _ ih =>
                    simp only [List.mem_cons, not_or] at hnot
                    exact .cons (by simp [beq_false_of_ne hnot.1, hfv]) (ih hnot.2)
                exact go hvNot hall
            · exact hcl0 w en' nm' fvs' htl
        have hml1 : CompactLocInv m1 ((v, vx) :: locOpt) := by
          rcases hm1 with rfl | ⟨u, hmc, huv, rfl⟩
          · exact hml0
          · intro tvar uvar hmem
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
              obtain ⟨n, w, huLoc, hw, rfl⟩ :=
                evalExpr_compactU32_inv spec hmc hx' henv evX'
              exact ⟨n, w, by simp [beq_false_of_ne (Ne.symm huv), huLoc], hw, by simp⟩
            · exact hml0 tvar uvar htl
        have evB := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
          fuel _ c1 m1 hatB0 halB0 hct1 hcl1 hmt1 hml1 hb henvB evB'
        rw [qualifyExprF_letValue]
        exact .letValue evX (matchPattern_bind_ok v vx) evB
    | wildcard | literal _ | tuple _ | array _ | construct _ _ _ =>
      rw [simpExpr_letValue_nonBind fuel a c m _ x b (fun _ hbad => by cases hbad)] at ev
      rw [qualifyExprF_letValue] at ev ⊢
      cases ev with | letValue evX' hmPat evB' =>
        rename_i val middle bs
        have hokVal := evalExpr_valOk hnd hHas hProv hLib spec hWT hx' henv evX'
        have hext := evX'.heap_extends
        have hbs := patHasTy_matchPattern hp hokVal hmPat
        have henvB := envOk_append hbs (henv.mono hext hext.length_le)
        have hdomBs := matchPattern_names_of_simple hp.isSimple hmPat
        have halB0 := aliasLocInv_shadow (ctors := c) (compacts := m) hdomBs hno2 hfreeBLoc
        have hcl0 := ctorLocInv_shadow (a := a) (m := m) hcl hdomBs
        have hml0 := compactLocInv_shadow (a := a) (c := c) hml hdomBs
        exact .letValue
          (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
            fuel a c m hatX halX hct hcl hmt hml hx henv evX')
          hmPat
          (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
            fuel _ _ _ hatB0 halB0 hct0 hcl0 hmt0 hml0 hb henvB evB')
    | global _ _ | load _ | orElse _ _ _ | «repeat» _ _ | record _ _ | constructAs _ _ _ _ => cases hp
  | fuel, a, c, m, ΓOrig, ΓOpt, locOrig, locOpt, .matchValue s arms, tb, h, h', r,
      hat, hal, hct, hcl, hmt, hml, .matchValue (ts := ts) hs harms, henv, ev => by
    have hatS : AliasTyInv a ΓOrig ΓOpt s :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1,
       fun z hz => hat.2 z (by simp [hasFreeVar, hz])⟩
    have halS : AliasLocInv a locOrig locOpt s :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.1,
       fun z hz => hal.2 z (by simp [hasFreeVar, hz])⟩
    have hatArms : AliasTyInvArms a ΓOrig ΓOpt arms :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.2,
       fun z hz => hat.2 z (by simp [hasFreeVar, hz])⟩
    have halArms : AliasLocInvArms a locOrig locOpt arms :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVar, Bool.or_eq_false_iff] at this; exact this.2,
       fun z hz => hal.2 z (by simp [hasFreeVar, hz])⟩
    have hs' := hasTy_simpExpr hSigs fuel a c m hatS hct hmt hs
    rcases simpExpr_matchValue_cases fuel a c m s arms with
      hres | ⟨fuel', enumTy, nm, fvs, binds, armBody, rfl, hsrc, hpick, _, hbvBinds, hres⟩
    · rw [hres] at ev
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
      cases ev with | matchValue evS' hsel evB' =>
        rename_i input middle bindings _
        have hokS := evalExpr_valOk hnd hHas hProv hLib spec hWT hs' henv evS'
        have hext := evS'.heap_extends
        have evS := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
          fuel a c m hatS halS hct hcl hmt hml hs henv evS'
        rw [map_qualifyArmsF, simpArms_eq_map, List.map_map] at hsel
        have hsel' : SourceSemantics.selectArm world [] middle input
            (arms.map fun arm => (qualifyPatF F arm.1,
              qualifyExprF F (let (a0, c0, m0) := shadowMaps (patBoundVars arm.1) a c m; simpExpr fuel a0 c0 m0 arm.2))) =
            .ok (some (bindings, _)) := hsel
        obtain ⟨p, b, hmem, rfl, hmPat, hselOrig⟩ :=
          selectArm_mapBody (fun p b => let (a0, c0, m0) := shadowMaps (patBoundVars p) a c m; simpExpr fuel a0 c0 m0 b) hsel'
        obtain ⟨Δ, hp, hb⟩ := harms.mem hmem
        have hbs := patHasTy_matchPattern hp hokS hmPat
        have henvB := envOk_append hbs (henv.mono hext hext.length_le)
        have hdomBs := matchPattern_names_of_simple hp.isSimple hmPat
        have hno2 : ∀ q ∈ a, q.2 ∉ patBoundVars p ∧ hasBoundVar q.2 b = false := by
          intro q hq
          have h0 := hatArms.1 q hq
          clear hselOrig hsel' hsel evB' evS evS' hs' hs hatS halS hat hal harms hatArms halArms hres
          induction arms with
          | nil => cases hmem
          | cons hd tl ih =>
            rcases hd with ⟨p0, b0⟩
            simp only [hasBoundVarArms, Bool.or_eq_false_iff] at h0
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
              exact ⟨(fun hm => by have := List.contains_iff_mem.mpr hm; rw [this] at h0; cases h0.1.1), h0.1.2⟩
            · exact ih htl h0.2
        have harmFree : ∀ z, z ∉ patBoundVars p → hasFreeVar z b = true →
            hasFreeVarArms z arms = true := by
          clear hselOrig hsel' hsel evB' evS evS' hs' hs hatS halS hat hal harms hatArms halArms hres
          intro z hnot hfz
          induction arms with
          | nil => cases hmem
          | cons hd tl ih =>
            rcases hd with ⟨p0, b0⟩
            simp only [hasFreeVarArms, Bool.or_eq_true]
            rcases List.mem_cons.mp hmem with heq | htl
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact Or.inl (by simp [hnot, hfz])
            · exact Or.inr (ih htl)
        have hatB0 := aliasTyInv_shadow (ctors := c) (compacts := m) hp.dom_eq hno2
          (fun z hnot hfz => hatArms.2 z (harmFree z hnot hfz))
        have halB0 := aliasLocInv_shadow (ctors := c) (compacts := m) hdomBs hno2
          (fun z hnot hfz => halArms.2 z (harmFree z hnot hfz))
        have hct0 := ctorTyInv_shadow (a := a) (m := m) hct hp.dom_eq
        have hcl0 := ctorLocInv_shadow (a := a) (m := m) hcl hdomBs
        have hmt0 := compactTyInv_shadow (a := a) (c := c) hmt hp.dom_eq
        have hml0 := compactLocInv_shadow (a := a) (c := c) hml hdomBs
        rw [← map_qualifyArmsF] at hselOrig
        exact .matchValue evS hselOrig
          (evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
            fuel _ _ _ hatB0 halB0 hct0 hcl0 hmt0 hml0 hb henvB evB')
    · rw [hres] at ev
      have hknown : ts = .named enumTy [] ∧
          ∃ vs fts,
            EvalExpr world [] locOpt (qualifyExprF F (simpExpr (fuel' + 1) a c m s)) h
              (.construct (qualifyName enumTy) nm vs) h ∧
            findCtorFields enums enumTy nm = some fts ∧
            List.Forall₂ (fun fv val => locOpt.find? (·.1 == fv) = some (fv, val)) fvs vs ∧
            List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs fts := by
        rcases hsrc with ⟨v, hscEq, hlk⟩ | ⟨args, hscEq, hav⟩
        · rw [hscEq] at hs'; cases hs' with | var hΓv =>
          obtain ⟨hvTy, fts, hctor, hfvTys⟩ := hct v enumTy nm fvs (mem_of_lookup_eq_some hlk)
          obtain ⟨vs, hvLoc, hfvLocs⟩ := hcl v enumTy nm fvs (mem_of_lookup_eq_some hlk)
          rw [hΓv, Option.some.injEq] at hvTy
          refine ⟨hvTy, vs, fts, ?_, hctor, hfvLocs, hfvTys⟩
          rw [hscEq, qualifyExprF_var]; exact .var hvLoc
        · rw [hscEq, allVarNames_inv hav] at hs'
          cases hs' with | construct _ _ _ _ hctor items =>
          have hfvTys := hasTyList_map_var_inv items
          have mkVs : ∀ {fvs0 : List String} {fts0 : List Lower.Ty},
              List.Forall₂ (fun fv ft => ΓOpt.lookup fv = some ft) fvs0 fts0 →
              ∃ vs0, List.Forall₂ (fun fv val => locOpt.find? (·.1 == fv) = some (fv, val)) fvs0 vs0 := by
            intro fvs0 fts0 hall
            induction hall with
            | nil => exact ⟨[], .nil⟩
            | @cons fv ft fvs1 fts1 hfv _ ih =>
              obtain ⟨val, hfound, _⟩ := henv fv ft hfv
              obtain ⟨vs1, hall1⟩ := ih
              exact ⟨val :: vs1, .cons hfound hall1⟩
          obtain ⟨vs, hfvLocs⟩ := mkVs hfvTys
          refine ⟨rfl, vs, _, ?_, hctor, hfvLocs, hfvTys⟩
          rw [hscEq, allVarNames_inv hav]
          simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
          rw [map_qualifyExprF]
          exact .construct (evalArgs_map_var_mk hfvLocs)
      obtain ⟨rfl, vs, fts, evScrut', hctor, hfvLocs, hfvTys⟩ := hknown
      have evScrut := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        (fuel' + 1) a c m hatS halS hct hcl hmt hml hs henv evScrut'
      obtain ⟨p, bs, Δ, hmem, hpPat, hb, hselOrig, hdomBs, hdomΔ, hlook⟩ :=
        selectArm_of_pickCtorArm (world := world) (h := h) hctor hfvLocs hfvTys harms hpick
      have harmFree : ∀ z, z ∉ patBoundVars p → hasFreeVar z armBody = true →
          hasFreeVarArms z arms = true := by
        clear hselOrig hpick hfvTys hfvLocs evScrut' evScrut hs' hs hatS halS hat hal harms hatArms halArms hres
        intro z hnot hfz
        induction arms with
        | nil => cases hmem
        | cons hd tl ih =>
          rcases hd with ⟨p0, b0⟩
          simp only [hasFreeVarArms, Bool.or_eq_true]
          rcases List.mem_cons.mp hmem with heq | htl
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact Or.inl (by simp [hnot, hfz])
          · exact Or.inr (ih htl)
      have harmBound : ∀ q ∈ a, hasBoundVar q.2 armBody = false := by
        intro q hq
        cases hbb : hasBoundVar q.2 armBody with
        | false => rfl
        | true =>
          have h0 := hatArms.1 q hq
          rw [hasBoundVarArms_of_mem hmem hbb] at h0
          cases h0
      have hnotBindsOfNone : ∀ z, binds.lookup z = none → z ∉ binds.map Prod.fst :=
        fun _ hnone => not_mem_map_fst_of_lookup_none hnone
      have hatB1 : AliasTyInv (binds ++ a.filter fun q => !(binds.map Prod.fst).contains q.1) (Δ ++ ΓOrig) ΓOpt armBody := by
        refine ⟨fun q hq => ?_, fun z hfz => ?_⟩
        · rcases List.mem_append.mp hq with h1 | h2
          · exact hbvBinds q h1
          · exact harmBound q (List.mem_filter.mp h2).1
        · rw [resolveAlias_append_filter]
          cases hlb : binds.lookup z with
          | some fv =>
            have hzMem : z ∈ Δ.map Prod.fst := by
              rw [hdomΔ]; exact List.mem_map.mpr ⟨(z, fv), mem_of_lookup_eq_some hlb, rfl⟩
            rw [lookup_append_of_mem_poly hzMem]
            exact (hlook z fv hlb).2
          | none =>
            have hzNotΔ : z ∉ Δ.map Prod.fst := by rw [hdomΔ]; exact hnotBindsOfNone z hlb
            have hzNotP : z ∉ patBoundVars p := by rw [← hpPat.dom_eq]; exact hzNotΔ
            rw [lookup_append_of_not_mem_poly hzNotΔ]
            exact hatArms.2 z (harmFree z hzNotP hfz)
      have halB1 : AliasLocInv (binds ++ a.filter fun q => !(binds.map Prod.fst).contains q.1) (bs ++ locOrig) locOpt armBody := by
        refine ⟨fun q hq => ?_, fun z hfz => ?_⟩
        · rcases List.mem_append.mp hq with h1 | h2
          · exact hbvBinds q h1
          · exact harmBound q (List.mem_filter.mp h2).1
        · rw [resolveAlias_append_filter]
          cases hlb : binds.lookup z with
          | some fv =>
            have hzMem : z ∈ bs.map Prod.fst := by
              rw [hdomBs]; exact List.mem_map.mpr ⟨(z, fv), mem_of_lookup_eq_some hlb, rfl⟩
            rw [find?_append_of_mem_poly hzMem]
            exact (hlook z fv hlb).1
          | none =>
            have hzNotBs : z ∉ bs.map Prod.fst := by rw [hdomBs]; exact hnotBindsOfNone z hlb
            have hzNotP : z ∉ patBoundVars p := by
              rw [← hpPat.dom_eq, hdomΔ]; exact hnotBindsOfNone z hlb
            rw [find?_append_of_not_mem_poly hzNotBs]
            exact halArms.2 z (harmFree z hzNotP hfz)
      have evArm := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel' _ c m hatB1 halB1 hct hcl hmt hml hb henv ev
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
      rw [← map_qualifyArmsF] at hselOrig
      exact .matchValue evScrut hselOrig evArm
termination_by fuel _ _ _ _ _ _ _ e _ _ _ _ _ _ _ _ _ _ _ _ _ => (fuel, sizeOf e)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hlt := List.sizeOf_lt_of_mem ‹(_, _) ∈ _›; simp only [Prod.mk.sizeOf_spec] at hlt; omega)

theorem evalArgs_simpExprList_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns) :
    ∀ (fuel : Nat) (a : AliasMap) (c : CtorMap) (m : AliasMap)
      {ΓOrig ΓOpt : TyEnv} {locOrig locOpt : Environment F Nat}
      {xs : List Expr} {ts : List Lower.Ty} {h h' : Heap F} {vs : List (SourceValue F)},
      AliasTyInvList a ΓOrig ΓOpt xs →
      AliasLocInvList a locOrig locOpt xs →
      CtorTyInv c enums ΓOpt →
      CtorLocInv c locOpt →
      CompactTyInv m ΓOpt →
      CompactLocInv m locOpt →
      HasTyList (fnSigsOf fns) enums ΓOrig xs ts →
      EnvOk enums h h.length ΓOpt locOpt →
      EvalArgs world [] locOpt ((simpExprList fuel a c m xs).map (qualifyExprF F)) h vs h' →
      EvalArgs world [] locOrig (xs.map (qualifyExprF F)) h vs h'
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .nil, _, ev => by
    rw [simpExprList] at ev; cases ev; exact .nil
  | fuel, a, c, m, _, _, _, _, _, _, _, _, _, hat, hal, hct, hcl, hmt, hml, .cons hd tl, henv, ev => by
    have hatH : AliasTyInv a _ _ _ :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVarList, Bool.or_eq_false_iff] at this; exact this.1,
       fun x hx => hat.2 x (by simp [hasFreeVarList, hx])⟩
    have halH : AliasLocInv a _ _ _ :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVarList, Bool.or_eq_false_iff] at this; exact this.1,
       fun x hx => hal.2 x (by simp [hasFreeVarList, hx])⟩
    have hatT : AliasTyInvList a _ _ _ :=
      ⟨fun q hq => by have := hat.1 q hq; simp only [hasBoundVarList, Bool.or_eq_false_iff] at this; exact this.2,
       fun x hx => hat.2 x (by simp [hasFreeVarList, hx])⟩
    have halT : AliasLocInvList a _ _ _ :=
      ⟨fun q hq => by have := hal.1 q hq; simp only [hasBoundVarList, Bool.or_eq_false_iff] at this; exact this.2,
       fun x hx => hal.2 x (by simp [hasFreeVarList, hx])⟩
    rw [simpExprList, List.map_cons] at ev
    cases ev with | cons evH evT =>
      have evH' := evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs
        fuel a c m hatH halH hct hcl hmt hml hd henv evH
      have hext := evH'.heap_extends
      exact .cons evH'
        (evalArgs_simpExprList_backward hnd hHas hProv hLib spec hWT hSigs
          fuel a c m hatT halT hct hcl hmt hml tl (henv.mono hext hext.length_le) evT)
termination_by fuel _ _ _ _ _ _ _ xs _ _ _ _ _ _ _ _ _ _ _ _ _ => (fuel, sizeOf xs)

end

/-- Clean top-level specialization of `evalExpr_simpExpr_backward` at empty maps `[] [] []`. -/
theorem evalExpr_simpExpr_empty_backward {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hWT : ProgWellTyped (fnSigsOf fns) enums fns) (hSigs : HasU32HelperSigs fns)
    (fuel : Nat) {Γ : TyEnv} {locals : Environment F Nat} {e : Expr} {t : Lower.Ty}
    {h h' : Heap F} {r : SourceValue F}
    (hty : HasTy (fnSigsOf fns) enums Γ e t)
    (henv : EnvOk enums h h.length Γ locals)
    (ev : EvalExpr world [] locals (qualifyExprF F (simpExpr fuel [] [] [] e)) h r h') :
    EvalExpr world [] locals (qualifyExprF F e) h r h' :=
  evalExpr_simpExpr_backward hnd hHas hProv hLib spec hWT hSigs fuel [] [] []
    ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
    ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
    (fun _ _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h)
    (fun _ _ h => by cases h)
    (fun _ _ h => by cases h)
    hty henv ev

end SimpExprEval

end SimpExprProof

/-! ## Section 9: Top-Level Composition (`inlineAndFoldOnce`, `optimizeFns`, `inlineFuse`) -/

section TopLevelComposition

/-! ### Part 9A: Program Invariant `ProgInlineFuseOk`, `overlayPreserving`, & `inlineAndFoldOnce_backward` -/

/-- Complete program invariant preserved across every round of `InlineFuse.inlineAndFoldOnce`:
distinct function names, well-typedness under `fnSigsOf fns`, standard `UInt32` helper
signatures, no shadowing (`NoLetShadow`), fresh inline-prefix counter `c` (`NoPrefixGe c`),
bounded literal arguments (`literalsBounded`), and no inlinable calls inside bounded-literal
arguments (`noInlinableInBoundedCalls`). -/
structure ProgInlineFuseOk (enums : List Aiur.Generic.EnumDecl) (fns : List Fn) (c : Nat) : Prop where
  nodup : (fns.map (·.name)).Nodup
  wellTyped : ProgWellTyped (fnSigsOf fns) enums fns
  u32Sigs : HasU32HelperSigs fns
  noShadow : ∀ f ∈ fns, NoLetShadow (f.params.map Prod.fst) f.body
  noPrefix : ∀ f ∈ fns,
    (∀ p ∈ f.params.map Prod.fst, NoPrefixGe c p) ∧ ExprNoPrefixGe c f.body
  litBounded : ∀ f ∈ fns, literalsBounded f.body = true
  noInlBounded : ∀ f ∈ fns, noInlinableInBoundedCalls f.body = true

private theorem fnSigsOf_eq_of_rel {fns fns' : List Fn}
    (hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result) fns fns') :
    fnSigsOf fns' = fnSigsOf fns := by
  funext qnm
  unfold fnSigsOf
  induction hrel with
  | nil => rfl
  | @cons f f' tl tl' h1 _ ih =>
    simp only [List.find?_cons, h1.1]
    cases (qualified f.name == qnm)
    · exact ih
    · simp only [h1.2.1, h1.2.2]

private theorem map_name_eq_of_rel {fns fns' : List Fn}
    (hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result) fns fns') :
    fns'.map (·.name) = fns.map (·.name) := by
  induction hrel with
  | nil => rfl
  | cons h1 _ ih => simp only [List.map_cons, h1.1, ih]

private theorem hasU32HelperSigs_of_eq {fns fns' : List Fn}
    (heq : fnSigsOf fns' = fnSigsOf fns) (h : HasU32HelperSigs fns) :
    HasU32HelperSigs fns' := by
  unfold HasU32HelperSigs at h ⊢
  rw [heq]; exact h

private theorem fixedHelpers_mem_of_rel {fns fns' : List Fn}
    (hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result ∧
      (IsFixedHelper f → f' = f)) fns fns') :
    ∀ f ∈ fns, IsFixedHelper f → f ∈ fns' := by
  induction hrel with
  | nil => intro _ hf; cases hf
  | cons h1 _ ih =>
    intro f hf hfix
    rcases List.mem_cons.mp hf with rfl | htl
    · rw [← h1.2.2.2 hfix]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih f htl hfix)

section OverlayPreserving

variable {F : Type} [Field F] [DecidableEq F]

/-- Proof-level intermediate world overlaying `fns` onto `base`, delegating verbatim to
`base.prepare` for every function still equal to one in `orig` (in particular every unchanged
`IsFixedHelper`), so `prepare` agrees on all arguments (even wrong-arity ones). -/
noncomputable def overlayPreserving (base : World F) (orig fns : List Fn) : World F where
  prepare nm args :=
    match fns.find? (fun f => qualified f.name == nm) with
    | some f =>
      letI := Classical.propDecidable (f ∈ orig)
      if _ : f ∈ orig then base.prepare nm args
      else if args.length == f.params.length then
        .ok ([], (f.params.map Prod.fst).zip args, qualifyExprF F f.body)
      else .error (.malformedValue (.tuple (args.map Value.type)))
    | none => base.prepare nm args
  typed := base.typed
  constant := base.constant
  constDepth := base.constDepth

omit [DecidableEq F] in
theorem sameAuxWorld_overlayPreserving (base : World F) (orig fns : List Fn) :
    SameAuxWorld (overlayPreserving base orig fns) base :=
  ⟨rfl, rfl, rfl⟩

omit [DecidableEq F] in
theorem overlayPreserving_prepare_nonProg (base : World F) (orig fns : List Fn)
    {nm : String} (hnp : isProgQName nm = false) (args : List (SourceValue F)) :
    (overlayPreserving base orig fns).prepare nm args = base.prepare nm args := by
  have hnone : fns.find? (fun f => qualified f.name == nm) = none := by
    rw [List.find?_eq_none]
    intro f _
    cases hq : (qualified f.name == nm)
    · simp
    · simp only [beq_iff_eq] at hq; subst hq; rw [isProgQName_qualified] at hnp; cases hnp
  simp [overlayPreserving, hnone]

omit [DecidableEq F] in
theorem overlayPreserving_prepare_orig (base : World F) {orig fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup) {f : Fn} (hf : f ∈ fns) (hOrig : f ∈ orig)
    (args : List (SourceValue F)) :
    (overlayPreserving base orig fns).prepare (qualified f.name) args =
      base.prepare (qualified f.name) args := by
  simp [overlayPreserving, find?_eq_of_nodup hnd hf, hOrig]

omit [DecidableEq F] in
theorem overlayPreserving_hasFns {base : World F} {orig fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup) (hOrigHas : WorldHasFns base orig) :
    WorldHasFns (overlayPreserving base orig fns) fns := by
  intro f hf args types locals expr hprep
  simp only [overlayPreserving, find?_eq_of_nodup hnd hf] at hprep
  split at hprep
  · next hOrig => exact hOrigHas f hOrig args types locals expr hprep
  · split at hprep
    · next hlen =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hprep
      obtain ⟨rfl, rfl, rfl⟩ := hprep
      simp only [beq_iff_eq] at hlen
      exact ⟨rfl, by simp [hlen], rfl, rfl⟩
    · cases hprep

omit [DecidableEq F] in
theorem overlayPreserving_providesFns {base : World F} {orig fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup) (hOrigProv : WorldProvidesFns base orig) :
    WorldProvidesFns (overlayPreserving base orig fns) fns := by
  intro f hf args hlen
  simp only [overlayPreserving, find?_eq_of_nodup hnd hf]
  split
  · next hOrig => exact hOrigProv f hOrig args hlen
  · have hlen' : args.length = f.params.length := by simpa using hlen
    simp [hlen']

theorem overlayPreserving_libSelfContained {base : World F} {orig fns : List Fn}
    (hLib : LibSelfContained base) :
    LibSelfContained (overlayPreserving base orig fns) := by
  intro w1 w2 nm args h h' r ha1 ha2 hn1 hn2 hnp ev
  exact hLib w1 w2 nm args h h' r
    (ha1.trans (sameAuxWorld_overlayPreserving base orig fns))
    (ha2.trans (sameAuxWorld_overlayPreserving base orig fns))
    (fun m a hm => (hn1 m a hm).trans (overlayPreserving_prepare_nonProg base orig fns hm a))
    (fun m a hm => (hn2 m a hm).trans (overlayPreserving_prepare_nonProg base orig fns hm a))
    hnp ev

theorem overlayPreserving_u32Spec {base : World F} {orig fns : List Fn}
    (hnd : (fns.map (·.name)).Nodup)
    (spec : U32WorldSpec base)
    (hLib : LibSelfContained base)
    (hHelp : HelpersSelfContained base orig)
    (hFixed : ∀ f ∈ orig, IsFixedHelper f → f ∈ fns) :
    U32WorldSpec (overlayPreserving base orig fns) :=
  spec.transfer hLib hHelp
    (sameAuxWorld_overlayPreserving base orig fns)
    (fun _ a hm => overlayPreserving_prepare_nonProg base orig fns hm a)
    (fun f hf hfix a => overlayPreserving_prepare_orig base hnd (hFixed f hf hfix) hf a)

end OverlayPreserving

section RoundAndOptimize

variable {F : Type} [Field F] [DecidableEq F]

/-- `buildInlineMap fns` satisfies `InlineMapValid` under `ProgInlineFuseOk` + `WorldProvidesFns`. -/
theorem buildInlineMap_valid {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} {c : Nat}
    (hok : ProgInlineFuseOk enums fns c)
    (hProv : WorldProvidesFns world fns) :
    InlineMapValid world (fnSigsOf fns) enums (buildInlineMap fns) where
  mem nm callee hlook := by
    have hmem := mem_of_lookup_eq_some hlook
    unfold buildInlineMap at hmem
    obtain ⟨f, hf, hfm⟩ := List.mem_filterMap.mp hmem
    split at hfm
    · next hcond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hfm
      obtain ⟨rfl, rfl⟩ := hfm
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      obtain ⟨⟨⟨⟨⟨⟨_, htp⟩, hst⟩, hnoCol⟩, hdist⟩, _⟩, _⟩ := hcond
      have htpNil : f.typeParams = [] := by
        cases h : f.typeParams with
        | nil => rfl
        | cons _ _ => simp [h] at htp
      have hsig : fnSigsOf fns (qualified f.name) = some (f.params.map Prod.snd, f.result) := by
        unfold fnSigsOf; rw [find?_eq_of_nodup hok.nodup hf]
      exact ⟨rfl, htpNil, hst, hnoCol, hdist, hsig, hProv f hf,
        hok.wellTyped f hf, hok.noShadow f hf, hok.litBounded f hf, hok.noInlBounded f hf⟩
    · cases hfm

private theorem inlineMapValid_filter {world : World F} {sigs : FnSigs}
    {enums : List Aiur.Generic.EnumDecl} {imap : List (String × Fn)} (p : String × Fn → Bool)
    (h : InlineMapValid world sigs enums imap) (hnd : (imap.map Prod.fst).Nodup) :
    InlineMapValid world sigs enums (imap.filter p) where
  mem nm callee hlook := by
    have hmem := (List.mem_filter.mp (mem_of_lookup_eq_some hlook)).1
    have hlkOrig : imap.lookup nm = some callee := by
      clear h hlook
      induction imap with
      | nil => cases hmem
      | cons hd tl ih =>
        rcases hd with ⟨k, v⟩
        simp only [List.map_cons, List.nodup_cons] at hnd
        simp only [List.lookup]
        rcases List.mem_cons.mp hmem with heq | htl
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; simp
        · have hne : nm ≠ k := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨(nm, callee), htl, rfl⟩)
          simp only [beq_false_of_ne hne]
          exact ih hnd.2 htl
    exact h.mem nm callee hlkOrig

private theorem buildInlineMap_nodup {fns : List Fn} (hnd : (fns.map (·.name)).Nodup) :
    ((buildInlineMap fns).map Prod.fst).Nodup := by
  unfold buildInlineMap
  induction fns with
  | nil => exact .nil
  | cons f tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.filterMap_cons]
    split
    · exact ih hnd.2
    · next b hb =>
      split at hb
      · simp only [Option.some.injEq] at hb; subst hb
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, ih hnd.2⟩
        obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hmem
        obtain ⟨g, hg, hfm⟩ := List.mem_filterMap.mp hq
        split at hfm
        · simp only [Option.some.injEq] at hfm; subst hfm; dsimp only at hq1
          exact hnd.1 (hq1 ▸ List.mem_map.mpr ⟨g, hg, rfl⟩)
        · cases hfm
      · cases hb

private def inlineFoldStep (imap : List (String × Fn)) (st : List Fn × Nat) (f : Fn) : List Fn × Nat :=
  let imapHere := imap.filter fun p => p.1 != f.name
  let (inlined, c') := (inlineCallsM imapHere f.body).run st.2
  let folded := simpExpr 32 [] [] [] inlined
  (st.1 ++ [{ f with body := folded }], c')

private theorem foldl_inlineFoldStep_spec {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} {imap : List (String × Fn)} {c0 : Nat}
    (hok : ProgInlineFuseOk enums fns c0)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world)
    (hvalid : InlineMapValid world (fnSigsOf fns) enums imap)
    (hndImap : (imap.map Prod.fst).Nodup) :
    ∀ (gs acc : List Fn) (c : Nat),
      c0 ≤ c →
      (∀ f ∈ gs, f ∈ fns) →
      let (res, c') := gs.foldl (inlineFoldStep imap) (acc, c)
      c ≤ c' ∧
      ∃ gs', res = acc ++ gs' ∧
        List.Forall₂ (fun f f' =>
          f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result ∧
          (IsFixedHelper f → f' = f) ∧
          HasTy (fnSigsOf fns) enums f'.params f'.body f'.result ∧
          NoLetShadow (f'.params.map Prod.fst) f'.body ∧
          ExprNoPrefixGe c' f'.body ∧
          literalsBounded f'.body = true ∧
          noInlinableInBoundedCalls f'.body = true ∧
          (∀ args h r h',
            List.Forall₂ (ValOk enums h h.length) (f.params.map Prod.snd) args →
            EvalExpr world [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f'.body) h r h' →
            EvalExpr world [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f.body) h r h')) gs gs'
  | [], acc, c, _, _ => ⟨Nat.le_refl c, [], by simp, .nil⟩
  | g :: rest, acc, c, hc0, hgs => by
    have hg : g ∈ fns := hgs g List.mem_cons_self
    let imapHere := imap.filter fun p => p.1 != g.name
    have hvHere : InlineMapValid world (fnSigsOf fns) enums imapHere :=
      inlineMapValid_filter _ hvalid hndImap
    have hclHere := inlineMapValid_closed hvHere
    have hnpG : (∀ p ∈ g.params.map Prod.fst, NoPrefixGe c p) ∧ ExprNoPrefixGe c g.body :=
      ⟨fun p hp => ((hok.noPrefix g hg).1 p hp).mono hc0, (hok.noPrefix g hg).2.mono hc0⟩
    have hinlVars := inlineCallsM_vars hclHere g.body c
    let inlined := ((inlineCallsM imapHere g.body).run c).1
    let c1 := ((inlineCallsM imapHere g.body).run c).2
    let folded := simpExpr 32 [] [] [] inlined
    let g' : Fn := { g with body := folded }
    have hcLe1 : c ≤ c1 := hinlVars.1
    have htyInl : HasTy (fnSigsOf fns) enums g.params inlined g.result :=
      hasTy_inlineCallsM hvHere c hnpG.2 (hok.wellTyped g hg)
    have hnsInl : NoLetShadow (g.params.map Prod.fst) inlined :=
      noLetShadow_inlineCallsM hvHere c hnpG.1 hnpG.2 (hok.noShadow g hg)
    have hnpInl : ExprNoPrefixGe c1 inlined :=
      exprNoPrefixGe_inlineCallsM hclHere hnpG.2
    have hlbInl := literalsBounded_inlineCallsM hvHere c (hok.litBounded g hg) (hok.noInlBounded g hg)
    have htyFold : HasTy (fnSigsOf fns) enums g.params folded g.result :=
      hasTy_simpExpr hok.u32Sigs 32 [] [] []
        ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) htyInl
    have hnsFold : NoLetShadow (g.params.map Prod.fst) folded :=
      noLetShadow_simpExpr 32 [] [] [] hnsInl
    have hnpFold : ExprNoPrefixGe c1 folded :=
      exprNoPrefixGe_simpExpr 32 [] [] [] (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hnpInl
    have hlbFold : literalsBounded folded = true := literalsBounded_simpExpr 32 [] [] [] hlbInl.1
    have hniFold : noInlinableInBoundedCalls folded = true := noInlinableInBoundedCalls_simpExpr 32 [] [] [] hlbInl.2
    have hfixG : IsFixedHelper g → g' = g := by
      intro hfix
      have hnames : ∀ nm cal, imapHere.lookup nm = some cal → (nm.startsWith "f" || nm.startsWith "jp") = true :=
        fun nm cal hl => (hvHere.mem nm cal hl).2.2.1
      have hinlEq : inlined = g.body := by
        have h1 := inlineCallsM_of_noInlinableCalls hnames c hfix.1
        exact congrArg Prod.fst h1
      have hfoldEq : folded = g.body := by
        show simpExpr 32 [] [] [] inlined = g.body
        rw [hinlEq, hfix.2.2]
      cases g; simp only [g', hfoldEq]
    have hsimG : ∀ args h r h',
        List.Forall₂ (ValOk enums h h.length) (g.params.map Prod.snd) args →
        EvalExpr world [] ((g.params.map Prod.fst).zip args) (qualifyExprF F folded) h r h' →
        EvalExpr world [] ((g.params.map Prod.fst).zip args) (qualifyExprF F g.body) h r h' := by
      intro args h r h' hargs ev
      have evInl := evalExpr_simpExpr_empty_backward hok.nodup hHas hProv hLib spec
        hok.wellTyped hok.u32Sigs 32 htyInl (envOk_zip hargs) ev
      exact evalExpr_inlineCallsM_backward hvHere c hnpG.2 (hok.wellTyped g hg) evInl
    have hstep : inlineFoldStep imap (acc, c) g = (acc ++ [g'], c1) := rfl
    simp only [List.foldl_cons, hstep]
    have ih := foldl_inlineFoldStep_spec hok hHas hProv hLib spec hvalid hndImap
      rest (acc ++ [g']) c1 (Nat.le_trans hc0 hcLe1) (fun f hf => hgs f (List.mem_cons_of_mem _ hf))
    dsimp only at ih ⊢
    obtain ⟨hc12, rest', hresEq, hrelRest⟩ := ih
    refine ⟨Nat.le_trans hcLe1 hc12, g' :: rest', by rw [hresEq, List.append_assoc]; rfl, ?_⟩
    exact .cons ⟨rfl, rfl, rfl, hfixG, htyFold, hnsFold, hnpFold.mono hc12, hlbFold, hniFold, hsimG⟩
      hrelRest

/-- One full round of `inlineAndFoldOnce` preserves `ProgInlineFuseOk`, leaves every
`IsFixedHelper` verbatim unchanged, and simulates every function body backward in `world`. -/
theorem inlineAndFoldOnce_props {world : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} {c : Nat}
    (hok : ProgInlineFuseOk enums fns c)
    (hHas : WorldHasFns world fns) (hProv : WorldProvidesFns world fns)
    (hLib : LibSelfContained world) (spec : U32WorldSpec world) :
    let (fns', c') := inlineAndFoldOnce fns c
    c ≤ c' ∧
    List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result ∧
      (IsFixedHelper f → f' = f)) fns fns' ∧
    fnSigsOf fns' = fnSigsOf fns ∧
    ProgInlineFuseOk enums fns' c' ∧
    (∀ f f', f ∈ fns → f' ∈ fns' →
      f'.name = f.name → f'.params = f.params → f'.result = f.result →
      ∀ args h r h',
        List.Forall₂ (ValOk enums h h.length) (f.params.map Prod.snd) args →
        EvalExpr world [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f'.body) h r h' →
        EvalExpr world [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f.body) h r h') := by
  by_cases hemp : (buildInlineMap fns).isEmpty = true
  · have heq : inlineAndFoldOnce fns c =
        (fns.map fun f => { f with body := simpExpr 16 [] [] [] f.body }, c) := by
      unfold inlineAndFoldOnce; simp only [hemp, ↓reduceIte]
    rw [heq]; dsimp only
    refine ⟨Nat.le_refl c, ?_, ?_, ?_, ?_⟩
    · refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun f _ => ⟨rfl, rfl, rfl, fun hfix => ?_⟩)
      have h16 := hfix.2.1
      cases f; simp only [h16]
    · exact fnSigsOf_eq_of_rel (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => ⟨rfl, rfl, rfl⟩))
    · have hsigsEq : fnSigsOf (fns.map fun f => { f with body := simpExpr 16 [] [] [] f.body }) = fnSigsOf fns :=
        fnSigsOf_eq_of_rel (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => ⟨rfl, rfl, rfl⟩))
      refine
        { nodup := by rw [List.map_map]; exact hok.nodup
          wellTyped := fun f' hf' => by
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
            rw [hsigsEq]
            exact hasTy_simpExpr hok.u32Sigs 16 [] [] []
              ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
              (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (hok.wellTyped f hf)
          u32Sigs := hasU32HelperSigs_of_eq hsigsEq hok.u32Sigs
          noShadow := fun f' hf' => by
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
            exact noLetShadow_simpExpr 16 [] [] [] (hok.noShadow f hf)
          noPrefix := fun f' hf' => by
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
            exact ⟨(hok.noPrefix f hf).1,
              exprNoPrefixGe_simpExpr 16 [] [] [] (fun _ h => by cases h) (fun _ h => by cases h)
                (fun _ h => by cases h) (hok.noPrefix f hf).2⟩
          litBounded := fun f' hf' => by
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
            exact literalsBounded_simpExpr 16 [] [] [] (hok.litBounded f hf)
          noInlBounded := fun f' hf' => by
            obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
            exact noInlinableInBoundedCalls_simpExpr 16 [] [] [] (hok.noInlBounded f hf) }
    · intro f f' hf hf' hnm _ _ args h r h' hargs ev
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
      have hfg : g = f := by
        have h1 := find?_eq_of_nodup hok.nodup hf
        have h2 := find?_eq_of_nodup hok.nodup hg
        rw [hnm] at h2; rw [h1, Option.some.injEq] at h2; exact h2.symm
      subst hfg
      exact evalExpr_simpExpr_empty_backward hok.nodup hHas hProv hLib spec
        hok.wellTyped hok.u32Sigs 16 (hok.wellTyped g hg) (envOk_zip hargs) ev
  · have heq : inlineAndFoldOnce fns c = fns.foldl (inlineFoldStep (buildInlineMap fns)) ([], c) := by
      unfold inlineAndFoldOnce; simp only [hemp]; rfl
    rw [heq]
    have hvalid := buildInlineMap_valid hok hProv
    have hndImap := buildInlineMap_nodup hok.nodup
    have hfold := foldl_inlineFoldStep_spec hok hHas hProv hLib spec hvalid hndImap
      fns [] c (Nat.le_refl c) (fun _ h => h)
    dsimp only at hfold ⊢
    obtain ⟨hcLe, fns', hresEq, hrel⟩ := hfold
    simp only [List.nil_append] at hresEq
    rw [hresEq]
    have hrel3 : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result) fns fns' :=
      hrel.imp fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩
    have hsigsEq := fnSigsOf_eq_of_rel hrel3
    have hnd' : (fns'.map (·.name)).Nodup := by rw [map_name_eq_of_rel hrel3]; exact hok.nodup
    have hmemProp : ∀ f' ∈ fns', ∃ f ∈ fns,
        f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result ∧
        HasTy (fnSigsOf fns) enums f'.params f'.body f'.result ∧
        NoLetShadow (f'.params.map Prod.fst) f'.body ∧
        ExprNoPrefixGe (fns.foldl (inlineFoldStep (buildInlineMap fns)) ([], c)).2 f'.body ∧
        literalsBounded f'.body = true ∧
        noInlinableInBoundedCalls f'.body = true ∧
        (∀ args h r h',
          List.Forall₂ (ValOk enums h h.length) (f.params.map Prod.snd) args →
          EvalExpr world [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f'.body) h r h' →
          EvalExpr world [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f.body) h r h') := by
      intro f' hf'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf'
      have hi' : i < fns.length := hrel.length_eq ▸ hi
      have h1 := (List.forall₂_iff_get.mp hrel).2 i hi' hi
      exact ⟨fns[i], List.getElem_mem hi', h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.2⟩
    refine ⟨hcLe, hrel.imp fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, hsigsEq, ?_, ?_⟩
    · refine
        { nodup := hnd'
          wellTyped := fun f' hf' => by
            obtain ⟨_, _, _, _, _, hty', _, _, _, _, _⟩ := hmemProp f' hf'
            rw [hsigsEq]; exact hty'
          u32Sigs := hasU32HelperSigs_of_eq hsigsEq hok.u32Sigs
          noShadow := fun f' hf' => (hmemProp f' hf').choose_spec.2.2.2.2.2.1
          noPrefix := fun f' hf' => by
            obtain ⟨f, hf, _, hpar, _, _, _, hnp', _, _, _⟩ := hmemProp f' hf'
            exact ⟨fun p hp => ((hok.noPrefix f hf).1 p (hpar ▸ hp)).mono hcLe, hnp'⟩
          litBounded := fun f' hf' => (hmemProp f' hf').choose_spec.2.2.2.2.2.2.2.1
          noInlBounded := fun f' hf' => (hmemProp f' hf').choose_spec.2.2.2.2.2.2.2.2.1 }
    · intro f f' hf hf' hnm _ _ args h r h' hargs ev
      obtain ⟨g, hg, hgnm, _, _, _, _, _, _, _, hsim⟩ := hmemProp f' hf'
      have hfg : g = f := by
        have h1 := find?_eq_of_nodup hok.nodup hf
        have h2 := find?_eq_of_nodup hok.nodup hg
        rw [← hgnm, hnm] at h2; rw [h1, Option.some.injEq] at h2; exact h2.symm
      subst hfg
      exact hsim args h r h' hargs ev

/-- **One-Round `inlineAndFoldOnce` Backward Simulation:**
Any `EvalFn` derivation in a world for `(inlineAndFoldOnce fns c).1` lifts backward to `wOrig`! -/
theorem inlineAndFoldOnce_backward {wOpt wOrig : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} {c : Nat}
    (hok : ProgInlineFuseOk enums fns c)
    (haux : SameAuxWorld wOpt wOrig)
    (hOptHas : WorldHasFns wOpt (inlineAndFoldOnce fns c).1)
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : ∀ m a, isProgQName m = false → wOpt.prepare m a = wOrig.prepare m a)
    (hLib : LibSelfContained wOrig) (spec : U32WorldSpec wOrig)
    {qnm : String} {ptys : List Lower.Ty} {rty : Lower.Ty}
    (hsig : fnSigsOf fns qnm = some (ptys, rty))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hargs : List.Forall₂ (ValOk enums h h.length) ptys args)
    (ev : EvalFn wOpt qnm args h r h') :
    EvalFn wOrig qnm args h r h' ∧ ValOk enums h' h'.length rty r := by
  have hprops := inlineAndFoldOnce_props hok hOrigHas hOrigProv hLib spec
  dsimp only at hprops
  obtain ⟨_, hrel, hsigsEq, hok', hsim⟩ := hprops
  exact world_transformBodies_typed_backward haux hok.nodup
    (hrel.imp fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    hOptHas hOrigProv hNonProg hLib spec
    (hsigsEq ▸ hok'.wellTyped) hsim hsig hargs ev

private def postInlineBody (body : Expr) : Expr :=
  let flat := flattenLets 4096 (simpExpr 32 [] [] [] body)
  foldConstU32OfField (Peephole.rewriteExpr (simpExpr 32 [] [] [] flat))

/-- **Top-Level `optimizeFns` Backward Simulation:**
Composes all 3 rounds of `inlineAndFoldOnce` (`inlineCallsM` + `simpExpr`) plus the final
5-stage pipeline (`simpExpr 32` → `flattenLets 4096` → `simpExpr 32` → `Peephole.rewriteExpr`
→ `foldConstU32OfField`) into one end-to-end backward simulation theorem! -/
theorem optimizeFns_backward {wOpt wOrig : World F} {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn}
    (hok0 : ProgInlineFuseOk enums fns 0)
    (haux : SameAuxWorld wOpt wOrig)
    (hOptHas : WorldHasFns wOpt (optimizeFns fns))
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : ∀ m a, isProgQName m = false → wOpt.prepare m a = wOrig.prepare m a)
    (hLib : LibSelfContained wOrig) (hHelp : HelpersSelfContained wOrig fns)
    (spec0 : U32WorldSpec wOrig)
    {qnm : String} {ptys : List Lower.Ty} {rty : Lower.Ty}
    (hsig : fnSigsOf fns qnm = some (ptys, rty))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hargs : List.Forall₂ (ValOk enums h h.length) ptys args)
    (ev : EvalFn wOpt qnm args h r h') :
    EvalFn wOrig qnm args h r h' ∧ ValOk enums h' h'.length rty r := by
  let p1 := inlineAndFoldOnce fns 0
  let p2 := inlineAndFoldOnce p1.1 p1.2
  let p3 := inlineAndFoldOnce p2.1 p2.2
  have hoptEq : optimizeFns fns = p3.1.map (fun f => { f with body := postInlineBody f.body }) := rfl
  rw [hoptEq] at hOptHas
  -- Round 1 properties in wOrig
  have hp1 := inlineAndFoldOnce_props hok0 hOrigHas hOrigProv hLib spec0
  dsimp only at hp1
  obtain ⟨_, hrel1, hsigs1, hok1, _⟩ := hp1
  have hfix1 : ∀ f ∈ fns, IsFixedHelper f → f ∈ p1.1 := fixedHelpers_mem_of_rel hrel1
  -- Intermediate world w1
  let w1 := overlayPreserving wOrig fns p1.1
  have hHas1 : WorldHasFns w1 p1.1 := overlayPreserving_hasFns hok1.nodup hOrigHas
  have hProv1 : WorldProvidesFns w1 p1.1 := overlayPreserving_providesFns hok1.nodup hOrigProv
  have hLib1 : LibSelfContained w1 := overlayPreserving_libSelfContained hLib
  have spec1 : U32WorldSpec w1 := overlayPreserving_u32Spec hok1.nodup spec0 hLib hHelp hfix1
  -- Round 2 properties in w1
  have hp2 := inlineAndFoldOnce_props hok1 hHas1 hProv1 hLib1 spec1
  dsimp only at hp2
  obtain ⟨_, hrel2, hsigs2, hok2, _⟩ := hp2
  have hfix2 : ∀ f ∈ fns, IsFixedHelper f → f ∈ p2.1 :=
    fun f hf hfix => fixedHelpers_mem_of_rel hrel2 f (hfix1 f hf hfix) hfix
  -- Intermediate world w2
  let w2 := overlayPreserving wOrig fns p2.1
  have hHas2 : WorldHasFns w2 p2.1 := overlayPreserving_hasFns hok2.nodup hOrigHas
  have hProv2 : WorldProvidesFns w2 p2.1 := overlayPreserving_providesFns hok2.nodup hOrigProv
  have hLib2 : LibSelfContained w2 := overlayPreserving_libSelfContained hLib
  have spec2 : U32WorldSpec w2 := overlayPreserving_u32Spec hok2.nodup spec0 hLib hHelp hfix2
  -- Round 3 properties in w2
  have hp3 := inlineAndFoldOnce_props hok2 hHas2 hProv2 hLib2 spec2
  dsimp only at hp3
  obtain ⟨_, hrel3, hsigs3, hok3, _⟩ := hp3
  have hfix3 : ∀ f ∈ fns, IsFixedHelper f → f ∈ p3.1 :=
    fun f hf hfix => fixedHelpers_mem_of_rel hrel3 f (hfix2 f hf hfix) hfix
  -- Intermediate world w3
  let w3 := overlayPreserving wOrig fns p3.1
  have hHas3 : WorldHasFns w3 p3.1 := overlayPreserving_hasFns hok3.nodup hOrigHas
  have hProv3 : WorldProvidesFns w3 p3.1 := overlayPreserving_providesFns hok3.nodup hOrigProv
  have hLib3 : LibSelfContained w3 := overlayPreserving_libSelfContained hLib
  have spec3 : U32WorldSpec w3 := overlayPreserving_u32Spec hok3.nodup spec0 hLib hHelp hfix3
  -- Step 1 (post-inlining 5-stage map): wOpt → w3
  have hsig3 : fnSigsOf p3.1 qnm = some (ptys, rty) := by rw [hsigs3, hsigs2, hsigs1]; exact hsig
  have hWTopt : ProgWellTyped (fnSigsOf p3.1) enums (p3.1.map fun f => { f with body := postInlineBody f.body }) := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
    have ht0 := hok3.wellTyped f hf
    have ht1 : HasTy (fnSigsOf p3.1) enums f.params (simpExpr 32 [] [] [] f.body) f.result :=
      hasTy_simpExpr hok3.u32Sigs 32 [] [] []
        ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) ht0
    have ht2 : HasTy (fnSigsOf p3.1) enums f.params (flattenLets 4096 (simpExpr 32 [] [] [] f.body)) f.result :=
      hasTy_flattenLets 4096 ht1
    have ht3 : HasTy (fnSigsOf p3.1) enums f.params
        (simpExpr 32 [] [] [] (flattenLets 4096 (simpExpr 32 [] [] [] f.body))) f.result :=
      hasTy_simpExpr hok3.u32Sigs 32 [] [] []
        ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) ht2
    exact hasTy_foldConst_rewriteExpr hok3.u32Sigs ht3
  have hBodySim3 : ∀ f f', f ∈ p3.1 → f' ∈ (p3.1.map fun g => { g with body := postInlineBody g.body }) →
      f'.name = f.name → f'.params = f.params → f'.result = f.result →
      ∀ args1 h1 r1 h2,
        List.Forall₂ (ValOk enums h1 h1.length) (f.params.map Prod.snd) args1 →
        EvalExpr w3 [] ((f.params.map Prod.fst).zip args1) (qualifyExprF F f'.body) h1 r1 h2 →
        EvalExpr w3 [] ((f.params.map Prod.fst).zip args1) (qualifyExprF F f.body) h1 r1 h2 := by
    intro f f' hf hf' hnm _ _ args1 h1 r1 h2 hargs1 evF
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
    have hfg : g = f := by
      have h1' := find?_eq_of_nodup hok3.nodup hf
      have h2' := find?_eq_of_nodup hok3.nodup hg
      rw [hnm] at h2'; rw [h1', Option.some.injEq] at h2'; exact h2'.symm
    subst hfg
    let e1 := simpExpr 32 [] [] [] g.body
    let e2 := flattenLets 4096 e1
    let e3 := simpExpr 32 [] [] [] e2
    have henv1 := envOk_zip hargs1
    have ht0 := hok3.wellTyped g hg
    have ht1 : HasTy (fnSigsOf p3.1) enums g.params e1 g.result :=
      hasTy_simpExpr hok3.u32Sigs 32 [] [] []
        ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) ht0
    have ht2 : HasTy (fnSigsOf p3.1) enums g.params e2 g.result := hasTy_flattenLets 4096 ht1
    have ht3 : HasTy (fnSigsOf p3.1) enums g.params e3 g.result :=
      hasTy_simpExpr hok3.u32Sigs 32 [] [] []
        ⟨(fun _ h => by cases h), fun _ _ => rfl⟩
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) ht2
    have hlb3 : literalsBounded e3 = true :=
      literalsBounded_simpExpr 32 [] [] [] (literalsBounded_flattenLets 4096
        (literalsBounded_simpExpr 32 [] [] [] (hok3.litBounded g hg)))
    have hns3 : NoLetShadow (g.params.map Prod.fst) e3 :=
      noLetShadow_simpExpr 32 [] [] [] (noLetShadow_flattenLets 4096
        (noLetShadow_simpExpr 32 [] [] [] (hok3.noShadow g hg)))
    -- 5. foldConstU32OfField backward
    have evRw : EvalExpr w3 [] ((g.params.map Prod.fst).zip args1) (qualifyExprF F (Peephole.rewriteExpr e3)) h1 r1 h2 :=
      evalExpr_foldConstU32OfField_backward spec3 evF
    -- 4. Peephole.rewriteExpr backward
    have ev3 : EvalExpr w3 [] ((g.params.map Prod.fst).zip args1) (qualifyExprF F e3) h1 r1 h2 :=
      evalExpr_peephole_backward hok3.nodup hHas3 hProv3 hLib3 spec3 hok3.wellTyped hok3.u32Sigs
        hlb3 hns3 ht3 henv1 evRw
    -- 3. simpExpr 32 backward
    have ev2 : EvalExpr w3 [] ((g.params.map Prod.fst).zip args1) (qualifyExprF F e2) h1 r1 h2 :=
      evalExpr_simpExpr_empty_backward hok3.nodup hHas3 hProv3 hLib3 spec3 hok3.wellTyped hok3.u32Sigs
        32 ht2 henv1 ev3
    -- 2. flattenLets 4096 backward
    have ev1 : EvalExpr w3 [] ((g.params.map Prod.fst).zip args1) (qualifyExprF F e1) h1 r1 h2 :=
      evalExpr_flattenLets_backward 4096 ht1.isClean ev2
    -- 1. simpExpr 32 backward
    exact evalExpr_simpExpr_empty_backward hok3.nodup hHas3 hProv3 hLib3 spec3 hok3.wellTyped hok3.u32Sigs
      32 ht0 henv1 ev1
  have hrelOpt : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params ∧ f'.result = f.result)
      p3.1 (p3.1.map fun f => { f with body := postInlineBody f.body }) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => ⟨rfl, rfl, rfl⟩)
  have ⟨evW3, _⟩ := world_transformBodies_typed_backward
    (haux.trans (sameAuxWorld_overlayPreserving wOrig fns p3.1).symm)
    hok3.nodup hrelOpt
    hOptHas hProv3
    (fun m a hm => (hNonProg m a hm).trans (overlayPreserving_prepare_nonProg wOrig fns p3.1 hm a).symm)
    hLib3 spec3 hWTopt hBodySim3 hsig3 hargs ev
  -- Step 2 (Round 3): w3 → w2
  have hsig2 : fnSigsOf p2.1 qnm = some (ptys, rty) := by rw [hsigs2, hsigs1]; exact hsig
  have ⟨evW2, _⟩ := inlineAndFoldOnce_backward hok2
    ((sameAuxWorld_overlayPreserving wOrig fns p3.1).trans (sameAuxWorld_overlayPreserving wOrig fns p2.1).symm)
    hHas3 hHas2 hProv2
    (fun m a hm => (overlayPreserving_prepare_nonProg wOrig fns p3.1 hm a).trans
      (overlayPreserving_prepare_nonProg wOrig fns p2.1 hm a).symm)
    hLib2 spec2 hsig2 hargs evW3
  -- Step 3 (Round 2): w2 → w1
  have hsig1 : fnSigsOf p1.1 qnm = some (ptys, rty) := by rw [hsigs1]; exact hsig
  have ⟨evW1, _⟩ := inlineAndFoldOnce_backward hok1
    ((sameAuxWorld_overlayPreserving wOrig fns p2.1).trans (sameAuxWorld_overlayPreserving wOrig fns p1.1).symm)
    hHas2 hHas1 hProv1
    (fun m a hm => (overlayPreserving_prepare_nonProg wOrig fns p2.1 hm a).trans
      (overlayPreserving_prepare_nonProg wOrig fns p1.1 hm a).symm)
    hLib1 spec1 hsig1 hargs evW2
  -- Step 4 (Round 1): w1 → wOrig
  exact inlineAndFoldOnce_backward hok0
    (sameAuxWorld_overlayPreserving wOrig fns p1.1)
    hHas1 hOrigHas hOrigProv
    (fun m a hm => overlayPreserving_prepare_nonProg wOrig fns p1.1 hm a)
    hLib spec0 hsig hargs evW1

private theorem optimizeFns_nodup {enums : List Aiur.Generic.EnumDecl}
    {fns : List Fn} {wOrig : World F}
    (hok0 : ProgInlineFuseOk enums fns 0)
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hLib : LibSelfContained wOrig) (hHelp : HelpersSelfContained wOrig fns)
    (spec0 : U32WorldSpec wOrig) :
    ((optimizeFns fns).map (·.name)).Nodup := by
  let p1 := inlineAndFoldOnce fns 0
  let p2 := inlineAndFoldOnce p1.1 p1.2
  let p3 := inlineAndFoldOnce p2.1 p2.2
  have hp1 := inlineAndFoldOnce_props hok0 hOrigHas hOrigProv hLib spec0
  dsimp only at hp1
  obtain ⟨_, hrel1, _, hok1, _⟩ := hp1
  let w1 := overlayPreserving wOrig fns p1.1
  have hp2 := inlineAndFoldOnce_props hok1 (overlayPreserving_hasFns hok1.nodup hOrigHas)
    (overlayPreserving_providesFns hok1.nodup hOrigProv) (overlayPreserving_libSelfContained hLib)
    (overlayPreserving_u32Spec hok1.nodup spec0 hLib hHelp (fixedHelpers_mem_of_rel hrel1))
  dsimp only at hp2
  obtain ⟨_, hrel2, _, hok2, _⟩ := hp2
  let w2 := overlayPreserving wOrig fns p2.1
  have hp3 := inlineAndFoldOnce_props hok2 (overlayPreserving_hasFns hok2.nodup hOrigHas)
    (overlayPreserving_providesFns hok2.nodup hOrigProv) (overlayPreserving_libSelfContained hLib)
    (overlayPreserving_u32Spec hok2.nodup spec0 hLib hHelp
      (fun f hf hfix => fixedHelpers_mem_of_rel hrel2 f (fixedHelpers_mem_of_rel hrel1 f hf hfix) hfix))
  dsimp only at hp3
  obtain ⟨_, _, _, hok3, _⟩ := hp3
  unfold optimizeFns
  dsimp only
  rw [List.map_map]
  exact hok3.nodup

/-- **Full `InlineFuse` (`pruneUnreachable roots (optimizeFns fns)`) Backward Simulation:**
Any `EvalFn` derivation in the final optimized & pruned world `wPruned` yields an `EvalFn`
derivation in the original `TypedLower` world `wOrig` with identical arguments, return value,
and heap — with zero intermediate world construction required by the caller! -/
theorem inlineFuse_backward {wPruned wOrig : World F} {enums : List Aiur.Generic.EnumDecl}
    {roots : List String} {fns : List Fn}
    (hok0 : ProgInlineFuseOk enums fns 0)
    (haux : SameAuxWorld wPruned wOrig)
    (hPrunedHas : WorldHasFns wPruned (pruneUnreachable roots (optimizeFns fns)))
    (hOnlyPruned : ∀ f ∈ optimizeFns fns, f ∉ pruneUnreachable roots (optimizeFns fns) →
      ∀ args res, wPruned.prepare (qualified f.name) args ≠ .ok res)
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : ∀ m a, isProgQName m = false → wPruned.prepare m a = wOrig.prepare m a)
    (hLib : LibSelfContained wOrig) (hHelp : HelpersSelfContained wOrig fns)
    (spec0 : U32WorldSpec wOrig)
    {qnm : String} {ptys : List Lower.Ty} {rty : Lower.Ty}
    (hsig : fnSigsOf fns qnm = some (ptys, rty))
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hargs : List.Forall₂ (ValOk enums h h.length) ptys args)
    (ev : EvalFn wPruned qnm args h r h') :
    EvalFn wOrig qnm args h r h' ∧ ValOk enums h' h'.length rty r := by
  have hndOpt := optimizeFns_nodup hok0 hOrigHas hOrigProv hLib hHelp spec0
  have evOpt : EvalFn (overlayWorld wPruned (optimizeFns fns)) qnm args h r h' :=
    pruneUnreachable_overlay_backward hndOpt hPrunedHas hOnlyPruned ev
  exact optimizeFns_backward hok0
    ((sameAuxWorld_overlayWorld wPruned (optimizeFns fns)).trans haux)
    (overlayWorld_hasFns wPruned hndOpt)
    hOrigHas hOrigProv
    (fun m a hm => (overlayWorld_prepare_nonProg wPruned (optimizeFns fns) hm a).trans (hNonProg m a hm))
    hLib hHelp spec0 hsig hargs evOpt

/-- **Entrypoint Specialization (`inlineFuse_entry_backward`):**
For any `Field`-only entrypoint `f ∈ fns` (e.g. `main0` taking `Field` / `[Field; N]` /
tuples of `Field`s), `ValOk` on arguments is discharged automatically — giving a clean,
assumption-free `EvalFn wPruned (qualified f.name) args h r h' → EvalFn wOrig (qualified f.name) args h r h'`! -/
theorem inlineFuse_entry_backward {wPruned wOrig : World F} {enums : List Aiur.Generic.EnumDecl}
    {roots : List String} {fns : List Fn}
    (hok0 : ProgInlineFuseOk enums fns 0)
    (haux : SameAuxWorld wPruned wOrig)
    (hPrunedHas : WorldHasFns wPruned (pruneUnreachable roots (optimizeFns fns)))
    (hOnlyPruned : ∀ f ∈ optimizeFns fns, f ∉ pruneUnreachable roots (optimizeFns fns) →
      ∀ args res, wPruned.prepare (qualified f.name) args ≠ .ok res)
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hNonProg : ∀ m a, isProgQName m = false → wPruned.prepare m a = wOrig.prepare m a)
    (hLib : LibSelfContained wOrig) (hHelp : HelpersSelfContained wOrig fns)
    (spec0 : U32WorldSpec wOrig)
    {f : Fn} (hf : f ∈ fns) (hfo : ∀ p ∈ f.params, isFieldOnlyTy p.2 = true)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hlen : args.length = f.params.length)
    (ev : EvalFn wPruned (qualified f.name) args h r h') :
    EvalFn wOrig (qualified f.name) args h r h' := by
  have hsig : fnSigsOf fns (qualified f.name) = some (f.params.map Prod.snd, f.result) := by
    unfold fnSigsOf; rw [find?_eq_of_nodup hok0.nodup hf]
  have hargs : List.Forall₂ (ValOk enums h h.length) (f.params.map Prod.snd) args := by
    refine List.forall₂_iff_get.mpr ⟨by simp [hlen], fun i hi1 hi2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_map]
    exact ValOk_of_isFieldOnlyTy args[i] (hfo f.params[i] (List.getElem_mem _))
  exact (inlineFuse_backward hok0 haux hPrunedHas hOnlyPruned hOrigHas hOrigProv
    hNonProg hLib hHelp spec0 hsig hargs ev).1

end RoundAndOptimize

end TopLevelComposition

end IxCC.AiurBackend.InlineFuseProof

#print axioms IxCC.AiurBackend.InlineFuseProof.pruneUnreachable_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.evalExpr_foldConstU32OfField_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.evalExpr_flattenLets_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.evalExpr_peephole_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.evalExpr_inlineCallsM_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.evalExpr_simpExpr_empty_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.inlineAndFoldOnce_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.optimizeFns_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.inlineFuse_backward
#print axioms IxCC.AiurBackend.InlineFuseProof.inlineFuse_entry_backward
