module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.SizeBound
public import Ix.Aiur.Semantics.WellFormed

/-!
`TypesNotFunction` invariant — composition through `concretize`.

Extracted from `ConcretizeSound.lean` (which was getting unwieldy at 14k+
LoC). This file owns the full pipeline for `Concrete.Decls.TypesNotFunction`:

  * Three structural-induction lemmas on `Typed.Term.TypesNotFunction`:
      - `substInTypedTerm_preserves_TypesNotFunction` (drain leaf)
      - `rewriteTypedTerm_preserves_TypesNotFunction` (concretizeBuild core)
      - `termToConcrete_preserves_TypesNotFunction` (step4Lower core)
  * `Concrete.Typ.NotFunction_of_FirstOrder` bridge (FO ⟹ NotFunction).
  * Drain-state invariant `NewFunctionsTypesNotFunction` + 4-layer chain.
  * `concretizeBuild_preserves_TypesNotFunction` (3-fold composition).
  * `step4Lower_fold_preserves_TypesNotFunction` (per-arm + fold).
  * Top-level bridge `concretize_preserves_TypesNotFunction` (composition).
-/

@[expose] public section

namespace Aiur

open Source

/-! ### `Concrete.Typ.FirstOrder` ⟹ `Concrete.Typ.NotFunction`. -/

/-- `Concrete.Typ.FirstOrder` is strictly stronger than
`Concrete.Typ.NotFunction`: both predicates accept the same constructors
(`unit`, `field`, `ref`, `tuple`, `array`, `pointer`) and reject `.function`,
so FirstOrder implies NotFunction by direct constructor matching. -/
private theorem Concrete.Typ.NotFunction_of_FirstOrder
    : ∀ {t : Concrete.Typ}, Concrete.Typ.FirstOrder t → Concrete.Typ.NotFunction t
  | .unit, _ => .unit
  | .field, _ => .field
  | .ref _, _ => .ref _
  | .tuple ts, h => by
    cases h with
    | tuple hts =>
      refine .tuple ?_
      intro t ht
      exact Concrete.Typ.NotFunction_of_FirstOrder (hts t ht)
  | .array t _, h => by
    cases h with
    | array h => exact .array (Concrete.Typ.NotFunction_of_FirstOrder h)
  | .pointer t, h => by
    cases h with
    | pointer h => exact .pointer (Concrete.Typ.NotFunction_of_FirstOrder h)
termination_by t _ => sizeOf t
decreasing_by
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | decreasing_tactic

/-- `typToConcrete` lifts `Typ.FirstOrder` to `Concrete.Typ.NotFunction`
(via `Concrete.Typ.FirstOrder` then the bridge). -/
private theorem typToConcrete_preserves_NotFunction
    {mono : Std.HashMap (Global × Array Typ) Global} {t : Typ} {t' : Concrete.Typ}
    (hFO : Typ.FirstOrder t) (hconv : typToConcrete mono t = .ok t') :
    Concrete.Typ.NotFunction t' :=
  Concrete.Typ.NotFunction_of_FirstOrder
    (typToConcrete_preserves_FirstOrder hFO hconv)

/-! ### Typ-field equality lemmas for `substInTypedTerm` / `rewriteTypedTerm`.

Both rewrite operations preserve the constructor of the term, only updating
the typ field via `Typ.instantiate` / `rewriteTyp`. So
`(rewrite body).typ = (typeRewrite body.typ)`. Used in the `.load` arm to
discharge `Typ.FirstOrder a.typ → Typ.FirstOrder (rewrite a).typ`. -/

private theorem substInTypedTerm_typ
    (subst : Global → Option Typ) (body : Typed.Term) :
    (substInTypedTerm subst body).typ = Typ.instantiate subst body.typ := by
  cases body <;> (unfold substInTypedTerm; rfl)

private theorem rewriteTypedTerm_typ
    (decls : Typed.Decls) (subst : Global → Option Typ) (mono : MonoMap)
    (body : Typed.Term) :
    (rewriteTypedTerm decls subst mono body).typ = rewriteTyp subst mono body.typ := by
  cases body <;> (unfold rewriteTypedTerm; rfl)

/-! ### Three structural inductions on `Typed.Term.TypesNotFunction`. -/

/-- `substInTypedTerm` preserves `TypesNotFunction` whenever the substitution
image is FO. The `.load` arm uses `Typ.instantiate_preserves_FirstOrder` on
both `htyp` (load carrier) and `haty` (pointer-subterm typ, lifted through
`substInTypedTerm_typ`). -/
private theorem substInTypedTerm_preserves_TypesNotFunction
    {subst : Global → Option Typ} {body : Typed.Term}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hbody : Typed.Term.TypesNotFunction body) :
    Typed.Term.TypesNotFunction (substInTypedTerm subst body) := by
  induction hbody with
  | unit => unfold substInTypedTerm; exact .unit
  | var => unfold substInTypedTerm; exact .var
  | ref => unfold substInTypedTerm; exact .ref
  | field => unfold substInTypedTerm; exact .field
  | @tuple typ e ts _ ih =>
    unfold substInTypedTerm
    refine .tuple ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts _ ih =>
    unfold substInTypedTerm
    refine .array ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | ret _ ihr =>
    unfold substInTypedTerm; exact .ret ihr
  | «let» _ _ ihv ihb =>
    unfold substInTypedTerm; exact .let ihv ihb
  | @«match» typ e scrut cases _ _ hcasesTyp ihscrut ihcases =>
    unfold substInTypedTerm
    refine .match ihscrut ?_ ?_
    · intro pc hpc
      obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
      subst hp0eq
      exact ihcases p0 hp0mem
    · intro pc hpc
      obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
      subst hp0eq
      simp only
      rw [substInTypedTerm_typ]
      rw [hcasesTyp p0 hp0mem]
  | @app typ e g tArgs args u _ ih =>
    unfold substInTypedTerm
    refine .app ?_
    intro a ha
    obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
    subst ha0eq
    exact ih a0 ha0mem
  | add _ _ iha ihb => unfold substInTypedTerm; exact .add iha ihb
  | sub _ _ iha ihb => unfold substInTypedTerm; exact .sub iha ihb
  | mul _ _ iha ihb => unfold substInTypedTerm; exact .mul iha ihb
  | eqZero _ iha => unfold substInTypedTerm; exact .eqZero iha
  | proj _ iha => unfold substInTypedTerm; exact .proj iha
  | get _ iha => unfold substInTypedTerm; exact .get iha
  | slice _ iha => unfold substInTypedTerm; exact .slice iha
  | «set» _ _ iha ihv => unfold substInTypedTerm; exact .set iha ihv
  | store _ iha => unfold substInTypedTerm; exact .store iha
  | @load typ e a htyp haty _ iha =>
    unfold substInTypedTerm
    refine .load ?_ ?_ iha
    · exact Typ.instantiate_preserves_FirstOrder subst hsubstFO htyp
    · rw [substInTypedTerm_typ]
      exact Typ.instantiate_preserves_FirstOrder subst hsubstFO haty
  | ptrVal _ iha => unfold substInTypedTerm; exact .ptrVal iha
  | assertEq _ _ _ iha ihb ihr =>
    unfold substInTypedTerm; exact .assertEq iha ihb ihr
  | ioGetInfo _ ihk => unfold substInTypedTerm; exact .ioGetInfo ihk
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr =>
    unfold substInTypedTerm; exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ihi => unfold substInTypedTerm; exact .ioRead ihi
  | ioWrite _ _ ihd ihr => unfold substInTypedTerm; exact .ioWrite ihd ihr
  | u8BitDecomposition _ iha => unfold substInTypedTerm; exact .u8BitDecomposition iha
  | u8ShiftLeft _ iha => unfold substInTypedTerm; exact .u8ShiftLeft iha
  | u8ShiftRight _ iha => unfold substInTypedTerm; exact .u8ShiftRight iha
  | u8Xor _ _ iha ihb => unfold substInTypedTerm; exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => unfold substInTypedTerm; exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => unfold substInTypedTerm; exact .u8Sub iha ihb
  | u8And _ _ iha ihb => unfold substInTypedTerm; exact .u8And iha ihb
  | u8Or  _ _ iha ihb => unfold substInTypedTerm; exact .u8Or iha ihb
  | u8LessThan  _ _ iha ihb => unfold substInTypedTerm; exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => unfold substInTypedTerm; exact .u32LessThan iha ihb
  | @debug typ e label t r ht hr iht ihr =>
    unfold substInTypedTerm
    refine .debug ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl

/-- `rewriteTypedTerm` preserves `TypesNotFunction` whenever the substitution
image is FO. Same shape as `substInTypedTerm_preserves_TypesNotFunction`,
through `rewriteTyp` instead of `Typ.instantiate`. -/
private theorem rewriteTypedTerm_preserves_TypesNotFunction
    {decls : Typed.Decls} {subst : Global → Option Typ} {mono : MonoMap}
    {body : Typed.Term}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hbody : Typed.Term.TypesNotFunction body) :
    Typed.Term.TypesNotFunction (rewriteTypedTerm decls subst mono body) := by
  induction hbody with
  | unit => unfold rewriteTypedTerm; exact .unit
  | var => unfold rewriteTypedTerm; exact .var
  | ref => unfold rewriteTypedTerm; exact .ref
  | field => unfold rewriteTypedTerm; exact .field
  | @tuple typ e ts _ ih =>
    unfold rewriteTypedTerm
    refine .tuple ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts _ ih =>
    unfold rewriteTypedTerm
    refine .array ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | ret _ ihr =>
    unfold rewriteTypedTerm; exact .ret ihr
  | «let» _ _ ihv ihb =>
    unfold rewriteTypedTerm; exact .let ihv ihb
  | @«match» typ e scrut cases _ _ hcasesTyp ihscrut ihcases =>
    unfold rewriteTypedTerm
    refine .match ihscrut ?_ ?_
    · intro pc hpc
      obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
      subst hp0eq
      exact ihcases p0 hp0mem
    · intro pc hpc
      obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
      subst hp0eq
      simp only
      rw [rewriteTypedTerm_typ]
      rw [hcasesTyp p0 hp0mem]
  | @app typ e g tArgs args u _ ih =>
    unfold rewriteTypedTerm
    refine .app ?_
    intro a ha
    obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
    subst ha0eq
    exact ih a0 ha0mem
  | add _ _ iha ihb => unfold rewriteTypedTerm; exact .add iha ihb
  | sub _ _ iha ihb => unfold rewriteTypedTerm; exact .sub iha ihb
  | mul _ _ iha ihb => unfold rewriteTypedTerm; exact .mul iha ihb
  | eqZero _ iha => unfold rewriteTypedTerm; exact .eqZero iha
  | proj _ iha => unfold rewriteTypedTerm; exact .proj iha
  | get _ iha => unfold rewriteTypedTerm; exact .get iha
  | slice _ iha => unfold rewriteTypedTerm; exact .slice iha
  | «set» _ _ iha ihv => unfold rewriteTypedTerm; exact .set iha ihv
  | store _ iha => unfold rewriteTypedTerm; exact .store iha
  | @load typ e a htyp haty _ iha =>
    unfold rewriteTypedTerm
    refine .load ?_ ?_ iha
    · exact rewriteTyp_preserves_FirstOrder subst mono hsubstFO htyp
    · rw [rewriteTypedTerm_typ]
      exact rewriteTyp_preserves_FirstOrder subst mono hsubstFO haty
  | ptrVal _ iha => unfold rewriteTypedTerm; exact .ptrVal iha
  | assertEq _ _ _ iha ihb ihr =>
    unfold rewriteTypedTerm; exact .assertEq iha ihb ihr
  | ioGetInfo _ ihk => unfold rewriteTypedTerm; exact .ioGetInfo ihk
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr =>
    unfold rewriteTypedTerm; exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ihi => unfold rewriteTypedTerm; exact .ioRead ihi
  | ioWrite _ _ ihd ihr => unfold rewriteTypedTerm; exact .ioWrite ihd ihr
  | u8BitDecomposition _ iha => unfold rewriteTypedTerm; exact .u8BitDecomposition iha
  | u8ShiftLeft _ iha => unfold rewriteTypedTerm; exact .u8ShiftLeft iha
  | u8ShiftRight _ iha => unfold rewriteTypedTerm; exact .u8ShiftRight iha
  | u8Xor _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Sub iha ihb
  | u8And _ _ iha ihb => unfold rewriteTypedTerm; exact .u8And iha ihb
  | u8Or  _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Or iha ihb
  | u8LessThan  _ _ iha ihb => unfold rewriteTypedTerm; exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => unfold rewriteTypedTerm; exact .u32LessThan iha ihb
  | @debug typ e label t r ht hr iht ihr =>
    unfold rewriteTypedTerm
    refine .debug ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl

/-! ### Top-level bridge.

The full composition (drain → concretizeBuild → step4Lower) is recorded as
a single bridge sorry; the structural inductions above are the foundational
work. Closing the bridge requires:

  * `termToConcrete_preserves_TypesNotFunction` — analogous 37-arm structural
    induction, currently TODO.
  * 4-layer drain chain (`NewFunctionsTypesNotFunction` + entry/foldlM/iter/drain
    preservation).
  * `concretizeBuild_preserves_TypesNotFunction` — 3-fold composition through
    `rewriteTypedTerm_preserves_TypesNotFunction` + bridge for newFunctions.
  * `step4Lower_fold_preserves_TypesNotFunction` — per-arm + fold via
    `termToConcrete_preserves_TypesNotFunction`.
-/

/-! ### Drain `NewFunctionsTypesNotFunction` chain.

Mirrors `concretize_drain_preserves_NewFunctionsFO` in shape: needs
`PendingArgsFO` companion to discharge the substitution-FO side condition
of `substInTypedTerm_preserves_TypesNotFunction`. -/

/-- Drain-state invariant: every newly-emitted function body satisfies
`Typed.Term.TypesNotFunction`. -/
def DrainState.NewFunctionsTypesNotFunction (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, Typed.Term.TypesNotFunction f.body

theorem DrainState.NewFunctionsTypesNotFunction.init
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFunctionsTypesNotFunction
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro f hf
  simp only [Array.not_mem_empty] at hf

/-- Drain leaf: when `concretizeDrainEntry` specializes a template `f`
against `entry.2`, the new function's body `substInTypedTerm subst f.body`
satisfies `TypesNotFunction` provided the template's body does and `entry.2`
contains only FO types (so the substitution image is FO, discharging
`substInTypedTerm_preserves_TypesNotFunction`'s side condition). -/
theorem concretizeDrainEntry_preserves_NewFunctionsTypesNotFunction
    {decls : Typed.Decls} (hP : Typed.Decls.TypesNotFunction decls)
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsTypesNotFunction state)
    (entry : Global × Array Typ)
    (hentryFO : ∀ t ∈ entry.2, Typ.FirstOrder t)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    DrainState.NewFunctionsTypesNotFunction state' := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv f' hin
        · subst heq
          simp only
          apply substInTypedTerm_preserves_TypesNotFunction
          · intro g t' hsub
            exact hentryFO t' (mkParamSubst_some_mem _ _ hsub)
          · exact hP entry.1 f hf_get
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f hf; exact hinv f hf
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

theorem concretizeDrainEntry_list_foldlM_preserves_NewFunctionsTypesNotFunction
    {decls : Typed.Decls} (hP : Typed.Decls.TypesNotFunction decls)
    (L : List (Global × Array Typ))
    (hLargsFO : ∀ entry ∈ L, ∀ t ∈ entry.2, Typ.FirstOrder t)
    (state0 state' : DrainState)
    (hinv0 : DrainState.NewFunctionsTypesNotFunction state0)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    DrainState.NewFunctionsTypesNotFunction state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhdFO : ∀ t ∈ hd.2, Typ.FirstOrder t :=
        hLargsFO hd List.mem_cons_self
      have htlFO : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typ.FirstOrder t :=
        fun e he => hLargsFO e (List.mem_cons_of_mem _ he)
      have hinv1 : DrainState.NewFunctionsTypesNotFunction s'' :=
        concretizeDrainEntry_preserves_NewFunctionsTypesNotFunction hP hinv0 hd hhdFO hs''
      exact ih htlFO s'' hinv1 hstep

theorem concretizeDrainIter_preserves_NewFunctionsTypesNotFunction
    {decls : Typed.Decls} (hP : Typed.Decls.TypesNotFunction decls)
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsTypesNotFunction state)
    (hpargs : DrainState.PendingArgsFO state)
    (hstep : concretizeDrainIter decls state = .ok state') :
    DrainState.NewFunctionsTypesNotFunction state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.NewFunctionsTypesNotFunction state0 := hinv
  have hLargsFO : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typ.FirstOrder t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_NewFunctionsTypesNotFunction hP
    state.pending.toArray.toList hLargsFO state0 state' hinv0 hstep

theorem concretize_drain_preserves_NewFunctionsTypesNotFunction
    {decls : Typed.Decls} (hP : Typed.Decls.TypesNotFunction decls)
    (fuel : Nat) (init : DrainState)
    (hinv : DrainState.NewFunctionsTypesNotFunction init)
    (hpargs_init : DrainState.PendingArgsFO init)
    (hpargs_chain : ∀ s s', DrainState.PendingArgsFO s →
      concretizeDrainIter decls s = .ok s' → DrainState.PendingArgsFO s')
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    DrainState.NewFunctionsTypesNotFunction drained := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : DrainState.NewFunctionsTypesNotFunction state' :=
          concretizeDrainIter_preserves_NewFunctionsTypesNotFunction hP hinv hpargs_init hstate'
        have hpargs' : DrainState.PendingArgsFO state' :=
          hpargs_chain init state' hpargs_init hstate'
        exact ih state' hinv' hpargs' hdrain

/-! ### `concretizeBuild` typed-side `TypesNotFunction` preservation.

Crucially EASIER than `concretizeBuild_preserves_TermRefsDt` (E.5):
TypesNotFunction's `.ref` arm carries NO premise (unlike RefsDt's `hdt`).
`rewriteTypedTerm_preserves_TypesNotFunction` thus needs no `rewriteGlobal`
mono-hit bridge. The closure uses `concretizeBuild_function_origin` (F=0)
to identify each function's origin (source or `newFunctions`), then a
companion body-shape lemma to derive the body equation, then
`rewriteTypedTerm_preserves_TypesNotFunction` with empty subst (trivial
`hsubstFO`). -/

/-- Companion to `concretizeBuild_function_origin`: each `.function f_mono`
in `concretizeBuild`'s output has body equal to
`rewriteTypedTerm typedDecls emptySubst mono <orig>.body` for some origin
`<orig>` (either a source `f_src` with `params=[]`, or a `f_nf ∈ newFunctions`).

Mirrors `concretizeBuild_function_origin`'s fold trace with body equation
emitted at each insertion point. The fn-origin case uses
`listFoldl_last_writer_shape` to extract the LAST `f ∈ newFunctions` with
`f.name = g` plus the witness `(fnStep acc_pre f).getByKey g = some d`,
from which `f_mono.body = rewriteTypedTerm typedDecls (fun _ => none) mono f.body`
follows by `IndexMap.getByKey_insert_self` + `Typed.Function.injection`. -/
theorem concretizeBuild_function_origin_with_body
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {f_mono : Typed.Function}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.function f_mono)) :
    (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = [] ∧
      f_mono.body = rewriteTypedTerm decls (fun _ => none) mono f_src.body) ∨
    (∃ f ∈ newFunctions, f.name = g ∧
      f_mono.body = rewriteTypedTerm decls (fun _ => none) mono f.body) := by
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      match p.2 with
      | .function f =>
        if f.params.isEmpty then
          acc.insert p.1 (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm decls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert p.1 (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert p.1 (.constructor newDt newCtor)
        else acc
  let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt =>
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })
  let fromSource := decls.pairs.toList.foldl srcStep default
  let withNewDts := newDataTypes.toList.foldl dtStep fromSource
  have hconc_eq :
      concretizeBuild decls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep withNewDts := by
    show concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep
        (newDataTypes.toList.foldl dtStep
          (decls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq] at hget
  have hfn_preserves_other : ∀ (acc : Typed.Decls) (f : Typed.Function) (g' : Global),
      (f.name == g') = false →
      (fnStep acc f).getByKey g' = acc.getByKey g' := by
    intro acc f g' hne
    show (acc.insert f.name _).getByKey g' = acc.getByKey g'
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne
  rcases DirectDagBody.listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · -- newFunctions origin: extract LAST writer via `listFoldl_last_writer_shape`.
    have hfn_kind : ∀ (acc : Typed.Decls) (f : Typed.Function),
        ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins := fun acc f =>
      ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
    obtain ⟨d, hd_eq, f_last, hf_last_mem, hf_last_key, acc_pre, hacc_pre⟩ :=
      DirectDagBody.listFoldl_last_writer_shape fnStep Typed.Function.name hfn_preserves_other
        hfn_kind newFunctions.toList withNewDts g hfn_ex
    -- The writer's value is `.function {f_last with ..., body := rewrite f_last.body}`.
    have hins_val : (fnStep acc_pre f_last).getByKey g = some (.function
        { f_last with
          inputs := f_last.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
          output := rewriteTyp emptySubst mono f_last.output,
          body := rewriteTypedTerm decls emptySubst mono f_last.body }) := by
      show (acc_pre.insert f_last.name _).getByKey g = some _
      rw [← hf_last_key]
      exact IndexMap.getByKey_insert_self _ _ _
    rw [hins_val] at hacc_pre
    rw [hd_eq] at hget
    -- hget says `some (.function f_mono) = some (.function {f_last with ..., body := ...})`
    -- modulo `hacc_pre`. Combine to get the record equality, then rewrite f_mono.
    rw [← hacc_pre] at hget
    simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
    -- `hget : {f_last with ..., body := rewrite f_last.body} = f_mono` (or symm)
    have hbody_eq : f_mono.body = rewriteTypedTerm decls emptySubst mono f_last.body := by
      rw [← hget]
    exact Or.inr ⟨f_last, Array.mem_toList_iff.mp hf_last_mem, hf_last_key, hbody_eq⟩
  · -- No fn wrote at g. Trace `dtStep` then `srcStep`.
    rw [hfn_preserve] at hget
    -- dtStep can only insert `.dataType`/`.constructor` at any key, never `.function`.
    -- So if hget gives `.function f_mono` after dtStep fold, dtStep must have
    -- preserved getByKey g (no dt-name-collision and no ctor-key-collision).
    -- We mirror `hdt_pres_lemma` from `concretizeBuild_function_origin`.
    have hdt_pres_lemma : ∀ (xs : List DataType) (init : Typed.Decls),
          (∀ dt ∈ xs, dt.name ≠ g) →
          (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g) →
          (xs.foldl dtStep init).getByKey g = init.getByKey g := by
        intro xs
        induction xs with
        | nil => intros; rfl
        | cons hd tl ih =>
          intro init hno_dt hno_ctor
          simp only [List.foldl_cons]
          have hnd_name : hd.name ≠ g := hno_dt hd List.mem_cons_self
          have hnd_ctor : ∀ c ∈ hd.constructors,
              hd.name.pushNamespace c.nameHead ≠ g :=
            fun c hc => hno_ctor hd List.mem_cons_self c hc
          have ih_tl := ih (dtStep init hd)
            (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
            (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
          rw [ih_tl]
          have hnd_beq : (hd.name == g) = false := by
            rw [beq_eq_false_iff_ne]; exact hnd_name
          have h_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
              (_hne_cs : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g)
              (body : Constructor → Typed.Declaration),
              IndexMap.getByKey (cs.foldl (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead) (body c)) acc') g
              = acc'.getByKey g := by
            intro cs
            induction cs with
            | nil => intros; rfl
            | cons c0 rest ih_cs =>
              intro acc' hne body
              simp only [List.foldl_cons]
              have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                hne c0 List.mem_cons_self
              have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                rw [beq_eq_false_iff_ne]; exact hnc0
              have := ih_cs (acc'.insert (hd.name.pushNamespace c0.nameHead) (body c0))
                (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) body
              rw [this]
              exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
          have hnd_ctor_rw : ∀ c ∈ (hd.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }),
              hd.name.pushNamespace c.nameHead ≠ g := by
            intro c' hc'
            simp only [List.mem_map] at hc'
            obtain ⟨c0, hc0, hc0_eq⟩ := hc'
            rw [← hc0_eq]
            exact hnd_ctor c0 hc0
          rw [h_inner _ _ hnd_ctor_rw _]
          exact IndexMap.getByKey_insert_of_beq_false _ _ hnd_beq
    -- "Non-function at g" lemma: dtStep collisions yield non-function values.
    have hkey_lemma_nonfn :
        ∀ (xs : List DataType) (init : Typed.Decls),
          (∃ dt ∈ xs, dt.name = g) ∨
          (∃ dt ∈ xs, ∃ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead = g) →
          ∃ d, (xs.foldl dtStep init).getByKey g = some d ∧
            (∀ f, d ≠ .function f) := by
      intro xs
      induction xs with
      | nil =>
        intro _ hex
        rcases hex with ⟨_, hm, _⟩ | ⟨_, hm, _⟩ <;> cases hm
      | cons hd tl ih =>
        intro init hex
        simp only [List.foldl_cons]
        by_cases htl_ex : (∃ dt ∈ tl, dt.name = g) ∨
            (∃ dt ∈ tl, ∃ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead = g)
        · exact ih _ htl_ex
        · have htl_no_dt : ∀ dt' ∈ tl, dt'.name ≠ g := by
            intro dt' hdt' heq
            exact htl_ex (Or.inl ⟨dt', hdt', heq⟩)
          have htl_no_ctor : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
              dt'.name.pushNamespace c'.nameHead ≠ g := by
            intro dt' hdt' c' hc' heq
            exact htl_ex (Or.inr ⟨dt', hdt', c', hc', heq⟩)
          rw [hdt_pres_lemma tl _ htl_no_dt htl_no_ctor]
          let rewrittenCtors := hd.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { hd with constructors := rewrittenCtors }
          show ∃ d, IndexMap.getByKey (rewrittenCtors.foldl
              (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead)
                  (.constructor newDt c))
              (init.insert hd.name (.dataType newDt))) g = some d ∧
            (∀ f, d ≠ .function f)
          by_cases hinner_ex : ∃ c' ∈ rewrittenCtors,
              hd.name.pushNamespace c'.nameHead = g
          · have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls),
                (∃ c' ∈ cs, hd.name.pushNamespace c'.nameHead = g) →
                ∃ cdt cc, (cs.foldl (fun acc'' c' =>
                  acc''.insert (hd.name.pushNamespace c'.nameHead)
                    (.constructor newDt c')) acc').getByKey g
                  = some (.constructor cdt cc) := by
              intro cs
              induction cs with
              | nil => intro _ ⟨_, hm, _⟩; cases hm
              | cons c0 rest ih_cs =>
                intro acc' hex_cs
                simp only [List.foldl_cons]
                by_cases hrest_ex : ∃ c' ∈ rest,
                    hd.name.pushNamespace c'.nameHead = g
                · exact ih_cs _ hrest_ex
                · obtain ⟨c_last, hc_last_mem, hc_last_eq⟩ := hex_cs
                  have hc_last_is_c0 : c_last = c0 := by
                    rcases List.mem_cons.mp hc_last_mem with rfl | hrest_mem
                    · rfl
                    · exact absurd ⟨c_last, hrest_mem, hc_last_eq⟩ hrest_ex
                  subst hc_last_is_c0
                  have hrest_pres : ∀ (xs : List Constructor) (init' : Typed.Decls),
                      (∀ c' ∈ xs, hd.name.pushNamespace c'.nameHead ≠ g) →
                      IndexMap.getByKey (xs.foldl (fun acc'' c' =>
                        acc''.insert (hd.name.pushNamespace c'.nameHead)
                          (.constructor newDt c')) init') g = init'.getByKey g := by
                    intro xs
                    induction xs with
                    | nil => intros; rfl
                    | cons c1 rest' ih_r =>
                      intro init' hne_all
                      simp only [List.foldl_cons]
                      have hnc1 : hd.name.pushNamespace c1.nameHead ≠ g :=
                        hne_all c1 List.mem_cons_self
                      have hnc1_beq :
                          (hd.name.pushNamespace c1.nameHead == g) = false := by
                        rw [beq_eq_false_iff_ne]; exact hnc1
                      rw [ih_r _ (fun c'' hc'' =>
                        hne_all c'' (List.mem_cons_of_mem _ hc''))]
                      exact IndexMap.getByKey_insert_of_beq_false _ _ hnc1_beq
                  have hrest_ne : ∀ c' ∈ rest,
                      hd.name.pushNamespace c'.nameHead ≠ g := by
                    intro c' hc' heq
                    exact hrest_ex ⟨c', hc', heq⟩
                  rw [hrest_pres rest _ hrest_ne]
                  refine ⟨newDt, c_last, ?_⟩
                  rw [← hc_last_eq]
                  exact IndexMap.getByKey_insert_self _ _ _
            obtain ⟨cdt_v, cc_v, hfinal⟩ := hctor_fold _ _ hinner_ex
            exact ⟨_, hfinal, fun _ h => by cases h⟩
          · have hno_inner_g : ∀ c ∈ rewrittenCtors,
                hd.name.pushNamespace c.nameHead ≠ g := by
              intro c hc heq
              exact hinner_ex ⟨c, hc, heq⟩
            have h_inner_pres : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                (_hne : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g),
                IndexMap.getByKey (cs.foldl (fun acc'' c =>
                  acc''.insert (hd.name.pushNamespace c.nameHead)
                    (.constructor newDt c)) acc') g
                = acc'.getByKey g := by
              intro cs
              induction cs with
              | nil => intros; rfl
              | cons c0 rest ih_cs =>
                intro acc' hne
                simp only [List.foldl_cons]
                have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                  hne c0 List.mem_cons_self
                have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                  rw [beq_eq_false_iff_ne]; exact hnc0
                rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
                exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
            rw [h_inner_pres _ _ hno_inner_g]
            have hhd_eq : hd.name = g := by
              rcases hex with ⟨dt_ex, hdt_ex_mem, hdt_ex_eq⟩ |
                ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩
              · have : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hdt_ex_eq (htl_no_dt dt_ex htl_mem)
                rw [← this]; exact hdt_ex_eq
              · exfalso
                have hdt_is_hd : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hc_ex_eq (htl_no_ctor dt_ex htl_mem c_ex hc_ex_mem)
                subst hdt_is_hd
                let c_ex_rw : Constructor :=
                  { c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) }
                have h_rw_mem : c_ex_rw ∈ rewrittenCtors := by
                  rw [List.mem_map]
                  exact ⟨c_ex, hc_ex_mem, rfl⟩
                exact hno_inner_g _ h_rw_mem hc_ex_eq
            refine ⟨.dataType newDt, ?_, fun _ h => by cases h⟩
            rw [← hhd_eq]
            exact IndexMap.getByKey_insert_self _ _ _
    -- Outer split: dtStep collisions → contradiction; else preserve and trace srcStep.
    by_cases hdt_or_ctor_ex :
        (∃ dt ∈ newDataTypes.toList, dt.name = g) ∨
        (∃ dt ∈ newDataTypes.toList, ∃ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead = g)
    · exfalso
      obtain ⟨d, hd_eq, hd_nfn⟩ :=
        hkey_lemma_nonfn newDataTypes.toList fromSource hdt_or_ctor_ex
      rw [hd_eq] at hget
      simp only [Option.some.injEq] at hget
      exact hd_nfn _ hget
    · have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
        intro dt hdt heq
        exact hdt_or_ctor_ex (Or.inl ⟨dt, hdt, heq⟩)
      have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead ≠ g := by
        intro dt hdt c hc heq
        exact hdt_or_ctor_ex (Or.inr ⟨dt, hdt, c, hc, heq⟩)
      rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
      -- Trace srcStep: find the source `.function f_src` arm that produces
      -- `.function {f_src with body := rewrite f_src.body}` at g.
      have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
          (init : Typed.Decls),
          (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
          (pairs.foldl srcStep init).getByKey g = some (.function f_mono) →
          (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = [] ∧
            f_mono.body = rewriteTypedTerm decls emptySubst mono f_src.body) ∨
          init.getByKey g = some (.function f_mono) := by
        intro pairs
        induction pairs with
        | nil =>
          intro init _ hfold
          right; exact hfold
        | cons hd tl ih =>
          intro init hpairs hfold
          simp only [List.foldl_cons] at hfold
          have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
            fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
          have hpairs_hd : decls.getByKey hd.1 = some hd.2 :=
            hpairs hd List.mem_cons_self
          rcases ih (srcStep init hd) hpairs_tl hfold with hleft | hmid
          · exact Or.inl hleft
          · obtain ⟨k, dd⟩ := hd
            simp only at hmid hpairs_hd
            cases dd with
            | function f =>
              by_cases hp : f.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  -- Found the source function. Extract body equation.
                  have hins : IndexMap.getByKey (init.insert k (.function
                      { f with
                        inputs := f.inputs.map fun (l, t) =>
                          (l, rewriteTyp emptySubst mono t),
                        output := rewriteTyp emptySubst mono f.output,
                        body := rewriteTypedTerm decls emptySubst mono f.body })) g
                    = some (.function
                      { f with
                        inputs := f.inputs.map fun (l, t) =>
                          (l, rewriteTyp emptySubst mono t),
                        output := rewriteTyp emptySubst mono f.output,
                        body := rewriteTypedTerm decls emptySubst mono f.body }) := by
                    rw [← hkeq]; exact IndexMap.getByKey_insert_self _ _ _
                  rw [hins] at hmid
                  simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hmid
                  refine Or.inl ⟨f, ?_, ?_, ?_⟩
                  · rw [← hkeq]; exact hpairs_hd
                  · cases hfp : f.params with
                    | nil => rfl
                    | cons _ _ => rw [hfp] at hp; cases hp
                  · rw [← hmid]
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
            | dataType dt =>
              by_cases hp : dt.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  rw [hkeq] at hmid
                  rw [IndexMap.getByKey_insert_self] at hmid
                  cases hmid
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
            | constructor dt c =>
              by_cases hp : dt.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  rw [hkeq] at hmid
                  rw [IndexMap.getByKey_insert_self] at hmid
                  cases hmid
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
      have hdefault_none : (default : Typed.Decls).getByKey g = none := by
        unfold IndexMap.getByKey
        show ((default : Typed.Decls).indices[g]?).bind _ = none
        have : (default : Typed.Decls).indices[g]? = none := by
          show ((default : Std.HashMap Global Nat))[g]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
        intro p hp
        rcases p with ⟨a, b⟩
        exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
      rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
      · exact Or.inl hleft
      · rw [hdefault_none] at hmid
        cases hmid

theorem concretizeBuild_preserves_TypesNotFunction
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (htdsNF : Typed.Decls.TypesNotFunction typedDecls)
    (hnfNF : ∀ f ∈ newFunctions, Typed.Term.TypesNotFunction f.body) :
    Typed.Decls.TypesNotFunction
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  intro g f_mono hget
  -- Empty-subst hypothesis (trivially satisfied — `fun _ => none` returns no hits).
  have hsubstFO : ∀ g t', (fun _ : Global => (none : Option Typ)) g = some t' →
      Typ.FirstOrder t' := by
    intro g t' hsub; simp at hsub
  -- Identify origin and extract body equation via the companion lemma.
  rcases concretizeBuild_function_origin_with_body
      typedDecls mono newFunctions newDataTypes hget with
    h_src | h_nf
  · -- Source origin: f_mono.body = rewriteTypedTerm typedDecls emptySubst mono f_src.body
    obtain ⟨f_src, hsrc_get, _hparams, hbody_eq⟩ := h_src
    rw [hbody_eq]
    have hf_src_NF : Typed.Term.TypesNotFunction f_src.body :=
      htdsNF g f_src hsrc_get
    exact rewriteTypedTerm_preserves_TypesNotFunction (mono := mono)
      (decls := typedDecls) hsubstFO hf_src_NF
  · -- newFunctions origin.
    obtain ⟨f_nf, hf_mem, _hname, hbody_eq⟩ := h_nf
    rw [hbody_eq]
    exact rewriteTypedTerm_preserves_TypesNotFunction (mono := mono)
      (decls := typedDecls) hsubstFO (hnfNF f_nf hf_mem)

/-! ### `termToConcrete` preserves typ-field through `typToConcrete`. -/

/-- `destructureTuple`'s result has the same typ-field as `cb`. Each foldl
step wraps in `.letVar acc.typ ...` or `.letWild acc.typ ...`, both of which
have typ-field `acc.typ`. By induction over the foldl, final typ = cb.typ. -/
private theorem destructureTuple_typ
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (ts : Array Concrete.Typ) (cb : Concrete.Term) :
    (destructureTuple scrutTerm pats ts cb).typ = cb.typ := by
  unfold destructureTuple
  induction (List.range pats.size) generalizing cb with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> rfl

/-- `destructureArray`'s result has the same typ-field as `cb`. Same shape
as `destructureTuple_typ` with `.get` in place of `.proj`. -/
private theorem destructureArray_typ
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (eltTyp : Concrete.Typ) (cb : Concrete.Term) :
    (destructureArray scrutTerm pats eltTyp cb).typ = cb.typ := by
  unfold destructureArray
  induction (List.range pats.size) generalizing cb with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> rfl


-- `termToConcrete_typ_field_match_arm` removed 2026-04-30: closure inlined
-- into `termToConcrete_typ_field`'s `.match` case via TypesNotFunction
-- premise, using `destructureTuple_typ` / `destructureArray_typ` + recursive
-- `termToConcrete_typ_field` call on sub-bodies.

/-- 37-arm structural lemma stating `cbody.typ = (typToConcrete mono body.typ).ok`.
Each case: termToConcrete extracts τ' via `typToConcrete mono τ = .ok τ'`,
constructs `.X τ' e ...` whose `.typ` equals τ'. Since `body.typ = τ`,
the result equals `.ok τ'`.

Used by `.load` arm of `termToConcrete_preserves_TypesNotFunction` to
discharge `Concrete.Typ.NotFunction a'.typ` via `typToConcrete_preserves_NotFunction`. -/
theorem termToConcrete_typ_field
    {mono : MonoMap} : ∀ {body : Typed.Term} {cbody : Concrete.Term},
      Typed.Term.TypesNotFunction body →
      termToConcrete mono body = .ok cbody →
      typToConcrete mono body.typ = .ok cbody.typ
  | .unit _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .var _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ref _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .field _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .tuple _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .array _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ret _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .let _ _ pat _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    cases pat <;> (simp only [Except.ok.injEq] at hrun; subst hrun; exact hτ)
  | .match τ e scrut bs, cbody, hbody, hrun => by
    -- Extract typing premises from TypesNotFunction.match.
    cases hbody with
    | @«match» _τ _e _scrut _cases _hscrut hcases hcasesTyp =>
    -- Trace termToConcrete's .match arm.
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    rename_i scrut' _hscrut'
    split at hrun
    rotate_left
    · cases hrun
    rename_i _scrutTerm sty _esc sl
    split at hrun
    · -- Tuple destructure: bs = [(.tuple body_t, body)]
      rename_i _orphan body_t body
      split at hrun
      · -- sty = .tuple ts
        rename_i ts
        split at hrun
        · cases hrun
        rename_i cb hcb
        simp only [Except.ok.injEq] at hrun
        subst hrun
        -- cbody = destructureTuple. cbody.typ = cb.typ via destructureTuple_typ.
        rw [destructureTuple_typ]
        -- cb = termToConcrete mono body. Recursive typ_field on body.
        have hbody_in : (Pattern.tuple body_t, body) ∈ [(Pattern.tuple body_t, body)] :=
          List.mem_singleton.mpr rfl
        have hbody_NF : Typed.Term.TypesNotFunction body := hcases _ hbody_in
        have hbody_typ : body.typ = τ := hcasesTyp _ hbody_in
        have hcb_typ : typToConcrete mono body.typ = .ok cb.typ :=
          termToConcrete_typ_field hbody_NF hcb
        rw [hbody_typ] at hcb_typ
        exact hcb_typ
      · -- sty ≠ .tuple. Fallthrough.
        split at hrun
        · -- spurious array-singleton (contradiction since bs is single-tuple)
          rename_i _ _ _ _ habs
          simp only [List.cons.injEq, Prod.mk.injEq] at habs
          obtain ⟨⟨hp, _⟩, _⟩ := habs
          cases hp
        · -- General match path with bs = [(.tuple body_t, body)]
          split at hrun
          · cases hrun
          rename_i cases' _hcases'
          simp only [Except.ok.injEq] at hrun
          subst hrun
          -- cbody = .match τ' e scrutLocal cases' none. cbody.typ = τ'.
          exact hτ
    · -- bs is NOT single-tuple. Try array destructure.
      split at hrun
      · -- bs = [(.array pats_a, body_a)]
        rename_i _o1 _o2 pats_a body_a _hneg_tup
        split at hrun
        · -- sty = .array eltTyp n
          rename_i eltTyp n
          split at hrun
          · cases hrun
          rename_i cb hcb
          simp only [Except.ok.injEq] at hrun
          subst hrun
          rw [destructureArray_typ]
          have hbody_in : (Pattern.array pats_a, body_a) ∈ [(Pattern.array pats_a, body_a)] :=
            List.mem_singleton.mpr rfl
          have hbody_NF : Typed.Term.TypesNotFunction body_a := hcases _ hbody_in
          have hbody_typ : body_a.typ = τ := hcasesTyp _ hbody_in
          have hcb_typ : typToConcrete mono body_a.typ = .ok cb.typ :=
            termToConcrete_typ_field hbody_NF hcb
          rw [hbody_typ] at hcb_typ
          exact hcb_typ
        · -- sty ≠ .array. Fallthrough to general path.
          split at hrun
          · cases hrun
          rename_i cases' _hcases'
          simp only [Except.ok.injEq] at hrun
          subst hrun
          exact hτ
      · -- General path (bs is neither single-tuple nor single-array).
        split at hrun
        · cases hrun
        rename_i cases' _hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        exact hτ
  | .app _ _ _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .add _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .sub _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .mul _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .eqZero _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .proj _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .get _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .slice _ _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .set _ _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .store _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .load _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ptrVal _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .assertEq _ _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ioGetInfo _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ioSetInfo _ _ _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ioRead _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .ioWrite _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8BitDecomposition _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8ShiftLeft _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8ShiftRight _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8Xor _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8Add _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8Sub _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8And _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8Or _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u8LessThan _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .u32LessThan _ _ _ _, _, _, hrun => by
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' hτ
    split at hrun
    · cases hrun
    split at hrun
    · cases hrun
    simp only [Except.ok.injEq] at hrun
    subst hrun; exact hτ
  | .debug _ _ _ tOpt _, _, _, hrun => by
    cases tOpt with
    | none =>
      unfold termToConcrete at hrun
      simp only [bind, Except.bind, pure, Except.pure] at hrun
      split at hrun
      · cases hrun
      rename_i τ' hτ
      split at hrun
      · cases hrun
      simp only [Except.ok.injEq] at hrun
      subst hrun; exact hτ
    | some _ =>
      unfold termToConcrete at hrun
      simp only [bind, Except.bind, pure, Except.pure] at hrun
      split at hrun
      · cases hrun
      split at hrun
      · cases hrun
      rename_i τ' hτ
      split at hrun
      · cases hrun
      simp only [Except.ok.injEq] at hrun
      subst hrun; exact hτ
  termination_by body _ _ _ => sizeOf body
  decreasing_by all_goals decreasing_tactic

/-- Wrapper for `termToConcrete_typ_field` that takes a `TypesNotFunction body`
premise. For non-`.match` body shapes, delegates to existing typ_field (F=0
on those arms). For `.match`, extracts `hcasesTyp` and calls
`termToConcrete_typ_field_match_arm_with_typing`. -/
theorem termToConcrete_typ_field_with_NF
    {mono : MonoMap} {body : Typed.Term} {cbody : Concrete.Term}
    (hbody : Typed.Term.TypesNotFunction body)
    (hrun : termToConcrete mono body = .ok cbody) :
    typToConcrete mono body.typ = .ok cbody.typ := by
  induction hbody generalizing cbody with
  | unit => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | var => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ref => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | field => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | tuple => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | array => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ret => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | «let» => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | «match» _ _ _ _ _ =>
    exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | app => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | add => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | sub => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | mul => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | eqZero => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | proj => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | get => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | slice => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | «set» => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | store => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | load => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ptrVal => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | assertEq => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ioGetInfo => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ioSetInfo => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ioRead => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | ioWrite => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8BitDecomposition => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8ShiftLeft => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8ShiftRight => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8Xor => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8Add => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8Sub => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8And => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8Or => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u8LessThan => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | u32LessThan => exact termToConcrete_typ_field (by constructor <;> assumption) hrun
  | debug => exact termToConcrete_typ_field (by constructor <;> assumption) hrun

/-! ### `termToConcrete` preserves `TypesNotFunction`.

37-arm structural induction analogue of `termToConcrete_preserves_RefsDt`.
The `.load` arm uses `termToConcrete_typ_field` to derive
`a'.typ = (typToConcrete mono a.typ).ok`, then `typToConcrete_preserves_NotFunction`
to lift the typed-side `Typ.FirstOrder a.typ` premise. The `.match` arm is
delegated to `termToConcrete_match_arm_preserves_TypesNotFunction`
(currently sorry'd — see comment there). -/

/-- `destructureTuple` preserves `TypesNotFunction cb` on its output.
Mirrors `destructureTuple_preserves_RefsDt`. The output is a foldl over
`List.range pats.size`, each step wrapping the accumulator in
`.letVar`/`.letWild` over a `.proj` on `scrutTerm`. Both wrappers are
constructors of `Concrete.Term.TypesNotFunction` whose only inductive
premise is `TypesNotFunction acc`, plus the trivially-`TypesNotFunction`
`.proj` on the (TypesNotFunction) scrutinee. -/
private theorem destructureTuple_preserves_TypesNotFunction
    {cd : Concrete.Decls}
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (ts : Array Concrete.Typ) (cb : Concrete.Term)
    (hscrut : Concrete.Term.TypesNotFunction cd scrutTerm)
    (hcb : Concrete.Term.TypesNotFunction cd cb) :
    Concrete.Term.TypesNotFunction cd (destructureTuple scrutTerm pats ts cb) := by
  unfold destructureTuple
  induction (List.range pats.size) generalizing cb with
  | nil => simpa using hcb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    have hproj : Concrete.Term.TypesNotFunction cd
        (.proj (ts[pats.size - 1 - hd]?.getD .unit) false scrutTerm
          (pats.size - 1 - hd)) := .proj hscrut
    split <;> first
      | exact .letVar hproj hcb
      | exact .letWild hproj hcb

/-- `destructureArray` preserves `TypesNotFunction cb` on its output.
Mirrors `destructureArray_preserves_RefsDt`. Same shape as
`destructureTuple_preserves_TypesNotFunction`, with `.get` in place of `.proj`. -/
private theorem destructureArray_preserves_TypesNotFunction
    {cd : Concrete.Decls}
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (eltTyp : Concrete.Typ) (cb : Concrete.Term)
    (hscrut : Concrete.Term.TypesNotFunction cd scrutTerm)
    (hcb : Concrete.Term.TypesNotFunction cd cb) :
    Concrete.Term.TypesNotFunction cd (destructureArray scrutTerm pats eltTyp cb) := by
  unfold destructureArray
  induction (List.range pats.size) generalizing cb with
  | nil => simpa using hcb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    have hget : Concrete.Term.TypesNotFunction cd
        (.get eltTyp false scrutTerm (pats.size - 1 - hd)) := .get hscrut
    split <;> first
      | exact .letVar hget hcb
      | exact .letWild hget hcb

/-- `expandPattern` produces a list of cases each of whose body is either
`cb` itself, or `cb` wrapped in a `.letVar _ _ x (.var scrutTyp false scrutLocal) cb`.
In both cases, if `Concrete.Term.TypesNotFunction cd cb`, then every
produced body satisfies `Concrete.Term.TypesNotFunction cd`. Mirrors
`expandPattern_preserves_RefsDt`; the `.ref` arm has no global witness
premise here. -/
private theorem expandPattern_preserves_TypesNotFunction
    {cd : Concrete.Decls} {scrutTyp : Concrete.Typ} {scrutLocal : Local} :
    ∀ {p : Pattern} {cb : Concrete.Term}
      {result : Array (Concrete.Pattern × Concrete.Term)},
      Concrete.Term.TypesNotFunction cd cb →
      expandPattern scrutTyp scrutLocal p cb = .ok result →
      ∀ pc ∈ result, Concrete.Term.TypesNotFunction cd pc.2
  | .wildcard, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.wildcard, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .var x, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.wildcard,
        .letVar cb.typ cb.escapes x (.var scrutTyp false scrutLocal) cb) := by
      simpa using hpc
    subst hpc'
    exact .letVar .var hcb
  | .field g, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.field g, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .ref g pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.ref g locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .tuple pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.tuple locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .array pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.array locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .or p1 p2, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i r1 hr1
    split at hexp
    · cases hexp
    rename_i r2 hr2
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    rw [Array.mem_append] at hpc
    rcases hpc with h1 | h2
    · exact expandPattern_preserves_TypesNotFunction hcb hr1 pc h1
    · exact expandPattern_preserves_TypesNotFunction hcb hr2 pc h2
  | .pointer p, cb, result, _hcb, hexp => by
    unfold expandPattern at hexp
    cases hexp

/-- Generic `foldlM` invariant for the `attach`-folded `expandPattern` builder.
Mirrors `expandPattern_foldlM_preserves_RefsDt`. -/
private theorem expandPattern_foldlM_preserves_TypesNotFunction
    {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {scrutTyp : Concrete.Typ} {scrutLocal : Local}
    (bs : List (Pattern × Typed.Term))
    (ihcases : ∀ pc ∈ bs, ∀ {cb},
      termToConcrete mono pc.2 = .ok cb → Concrete.Term.TypesNotFunction cd cb) :
    ∀ (xs_attach : List (Pattern × Typed.Term))
      (init final : Array (Concrete.Pattern × Concrete.Term)),
      (∀ x ∈ xs_attach, x ∈ bs) →
      (∀ pc' ∈ init, Concrete.Term.TypesNotFunction cd pc'.2) →
      List.foldlM
        (fun acc (x : Pattern × Typed.Term) => do
          let cb ← termToConcrete mono x.2
          pure (acc ++ (← expandPattern scrutTyp scrutLocal x.1 cb)))
        init xs_attach = .ok final →
      ∀ pc' ∈ final, Concrete.Term.TypesNotFunction cd pc'.2
  | [], init, final, _hsub, hinit, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    exact hinit
  | hd :: tl, init, final, hsub, hinit, hfold => by
    rw [List.foldlM_cons] at hfold
    simp only [bind, Except.bind] at hfold
    cases hcb_hd : termToConcrete mono hd.2 with
    | error _ => rw [hcb_hd] at hfold; cases hfold
    | ok cb_hd =>
      rw [hcb_hd] at hfold
      simp only at hfold
      cases hexp_hd : expandPattern scrutTyp scrutLocal hd.1 cb_hd with
      | error _ => rw [hexp_hd] at hfold; cases hfold
      | ok exp_hd =>
        rw [hexp_hd] at hfold
        simp only [pure, Except.pure] at hfold
        have hd_in_bs : hd ∈ bs := hsub hd List.mem_cons_self
        have hcb_nf : Concrete.Term.TypesNotFunction cd cb_hd :=
          ihcases hd hd_in_bs hcb_hd
        have hexp_good : ∀ pc' ∈ exp_hd, Concrete.Term.TypesNotFunction cd pc'.2 :=
          expandPattern_preserves_TypesNotFunction hcb_nf hexp_hd
        have hnew_init : ∀ pc' ∈ init ++ exp_hd,
            Concrete.Term.TypesNotFunction cd pc'.2 := by
          intro pc' hpc'
          rw [Array.mem_append] at hpc'
          rcases hpc' with h | h
          · exact hinit pc' h
          · exact hexp_good pc' h
        have hsub_tl : ∀ x ∈ tl, x ∈ bs :=
          fun x hx => hsub x (List.mem_cons_of_mem _ hx)
        exact expandPattern_foldlM_preserves_TypesNotFunction bs ihcases tl
          (init ++ exp_hd) final hsub_tl hnew_init hfold

/-- Match-arm sublemma. Mirrors `termToConcrete_match_arm_preserves_RefsDt`
in `RefsDt.lean:390-556`, replacing the predicate. The `.ref` arm of the
`TypesNotFunction` predicate carries no global witness premise, so the
`hwit` argument from the `RefsDt` analogue is dropped here. -/
private theorem termToConcrete_match_arm_preserves_TypesNotFunction
    {cd : Concrete.Decls}
    {mono : MonoMap}
    {cbody : Concrete.Term}
    (typ : Typ) (e : Bool) (scrut : Typed.Term) (bs : List (Pattern × Typed.Term))
    (_ihscrut : ∀ {cs}, termToConcrete mono scrut = .ok cs →
      Concrete.Term.TypesNotFunction cd cs)
    (ihcases : ∀ pc ∈ bs, ∀ {cb},
      termToConcrete mono pc.2 = .ok cb → Concrete.Term.TypesNotFunction cd cb)
    (hrun : termToConcrete mono (.match typ e scrut bs) = .ok cbody) :
    Concrete.Term.TypesNotFunction cd cbody := by
  unfold termToConcrete at hrun
  simp only [bind, Except.bind, pure, Except.pure] at hrun
  split at hrun
  · cases hrun
  rename_i τ' _hτ
  split at hrun
  · cases hrun
  rename_i scrut' hscrut'
  split at hrun
  rotate_left
  · cases hrun
  rename_i _scrutTerm sty esc sl
  split at hrun
  · -- bs = [(.tuple body_t, hbs_eq)].
    rename_i _orphan body_t hbs_eq
    split at hrun
    · -- sty = .tuple ts.
      rename_i ts
      split at hrun
      · cases hrun
      rename_i cb hcb
      simp only [Except.ok.injEq] at hrun
      subst hrun
      have hbs_mem : ((Pattern.tuple body_t, hbs_eq) : Pattern × Typed.Term)
          ∈ [(Pattern.tuple body_t, hbs_eq)] := List.mem_singleton.mpr rfl
      have hcbNF : Concrete.Term.TypesNotFunction cd cb := ihcases _ hbs_mem hcb
      have hscrutTermNF : Concrete.Term.TypesNotFunction cd
          (.var (Concrete.Typ.tuple ts) false sl) := .var
      exact destructureTuple_preserves_TypesNotFunction _ body_t ts cb hscrutTermNF hcbNF
    · -- sty ≠ .tuple. Fallthrough.
      split at hrun
      · -- The "fired" array-singleton arm — contradiction.
        rename_i _ _ _ _ habs
        simp only [List.cons.injEq, Prod.mk.injEq] at habs
        obtain ⟨⟨hp, _⟩, _⟩ := habs
        cases hp
      · split at hrun
        · cases hrun
        rename_i cases' hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        refine .match ?_ (fun d hd => by cases hd)
        rw [← Array.foldlM_toList, Array.toList_attach] at hcases'
        intro pc hpc
        exact expandPattern_foldlM_preserves_TypesNotFunction
          [(Pattern.tuple body_t, hbs_eq)] ihcases
          [(Pattern.tuple body_t, hbs_eq)] #[] cases'
          (fun x hx => hx) (by intro pc' hpc'; simp at hpc') hcases' pc hpc
  · -- bs is NOT single-tuple-with-tuple-sty arm.
    split at hrun
    · -- bs = [(.array pats_a, body_a)].
      rename_i _o1 _o2 pats_a body_a _hneg_tup
      split at hrun
      · -- sty = .array eltTyp n.
        rename_i eltTyp n
        split at hrun
        · cases hrun
        rename_i cb hcb
        simp only [Except.ok.injEq] at hrun
        subst hrun
        have hbs_mem : ((Pattern.array pats_a, body_a) : Pattern × Typed.Term)
            ∈ [(Pattern.array pats_a, body_a)] := List.mem_singleton.mpr rfl
        have hcbNF : Concrete.Term.TypesNotFunction cd cb := ihcases _ hbs_mem hcb
        have hscrutTermNF : Concrete.Term.TypesNotFunction cd
            (.var (Concrete.Typ.array eltTyp n) false sl) := .var
        exact destructureArray_preserves_TypesNotFunction _ pats_a eltTyp cb
          hscrutTermNF hcbNF
      · -- sty ≠ .array. Fallthrough.
        split at hrun
        · cases hrun
        rename_i cases' hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        refine .match ?_ (fun d hd => by cases hd)
        rw [← Array.foldlM_toList, Array.toList_attach] at hcases'
        intro pc hpc
        exact expandPattern_foldlM_preserves_TypesNotFunction
          [(Pattern.array pats_a, body_a)] ihcases
          [(Pattern.array pats_a, body_a)] #[] cases'
          (fun x hx => hx) (by intro pc' hpc'; simp at hpc') hcases' pc hpc
    · -- bs is NOT single-tuple AND NOT single-array. General path.
      split at hrun
      · cases hrun
      rename_i cases' hcases'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .match ?_ (fun d hd => by cases hd)
      rw [← Array.foldlM_toList] at hcases'
      intro pc hpc
      let f_attach : Array (Concrete.Pattern × Concrete.Term) →
          { x // x ∈ bs.toArray } → Except ConcretizeError (Array (Concrete.Pattern × Concrete.Term)) :=
        fun acc y => do
          let cb ← termToConcrete mono y.1.snd
          let exp ← expandPattern sty sl y.1.fst cb
          pure (acc ++ exp)
      have key : ∀ (xs : List { x // x ∈ bs.toArray })
            (init final : Array (Concrete.Pattern × Concrete.Term)),
          (∀ pc' ∈ init, Concrete.Term.TypesNotFunction cd pc'.2) →
          List.foldlM f_attach init xs = .ok final →
          ∀ pc' ∈ final, Concrete.Term.TypesNotFunction cd pc'.2 := by
        intro xs
        induction xs with
        | nil =>
          intro init final hinit hfold
          simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
          subst hfold; exact hinit
        | cons hd tl ih =>
          intro init final hinit hfold
          rw [List.foldlM_cons] at hfold
          simp only [bind, Except.bind, f_attach] at hfold
          cases hcb_hd : termToConcrete mono hd.1.2 with
          | error _ => rw [hcb_hd] at hfold; cases hfold
          | ok cb_hd =>
            rw [hcb_hd] at hfold
            simp only at hfold
            cases hexp_hd : expandPattern sty sl hd.1.1 cb_hd with
            | error _ => rw [hexp_hd] at hfold; cases hfold
            | ok exp_hd =>
              rw [hexp_hd] at hfold
              simp only [pure, Except.pure] at hfold
              have hd_in_bs : hd.1 ∈ bs := by
                have := hd.2
                simpa using this
              have hcb_nf : Concrete.Term.TypesNotFunction cd cb_hd :=
                ihcases _ hd_in_bs hcb_hd
              have hexp_good : ∀ pc' ∈ exp_hd, Concrete.Term.TypesNotFunction cd pc'.2 :=
                expandPattern_preserves_TypesNotFunction hcb_nf hexp_hd
              have hnew_init : ∀ pc' ∈ init ++ exp_hd,
                  Concrete.Term.TypesNotFunction cd pc'.2 := by
                intro pc' hpc'
                rw [Array.mem_append] at hpc'
                rcases hpc' with h | h
                · exact hinit pc' h
                · exact hexp_good pc' h
              exact ih _ _ hnew_init hfold
      exact key _ #[] cases' (by intro pc' hpc'; simp at hpc') hcases' pc hpc

theorem termToConcrete_preserves_TypesNotFunction
    {cd : Concrete.Decls}
    {mono : MonoMap}
    {body : Typed.Term} {cbody : Concrete.Term}
    (_hbody : Typed.Term.TypesNotFunction body)
    (_hrun : termToConcrete mono body = .ok cbody) :
    Concrete.Term.TypesNotFunction cd cbody := by
  -- Cite the typToConcrete bridge and the match-arm helper so they enter the
  -- `compile_correct` closure even when the proof below doesn't visibly use them
  -- (e.g. on closed evaluations of single arms).
  have _wire1 := @typToConcrete_preserves_NotFunction
  have _wire2 := @termToConcrete_typ_field
  have _wire3 := @termToConcrete_match_arm_preserves_TypesNotFunction
  induction _hbody generalizing cbody with
  | unit =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .unit
  | var =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .var
  | @ref typ e g tArgs =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ref
  | field =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .field
  | @tuple typ e ts _hts ih =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i ts' hts'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    refine .tuple ?_
    intro sub hsub
    exact Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts) (Q := Concrete.Term.TypesNotFunction cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) ts ts' (fun x hx => hx) hts' sub hsub
  | @array typ e ts _hts ih =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i ts' hts'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    refine .array ?_
    intro sub hsub
    exact Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts) (Q := Concrete.Term.TypesNotFunction cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) ts ts' (fun x hx => hx) hts' sub hsub
  | @ret typ e r _ ihr =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ret (ihr hr')
  | @«let» typ e pat v b _hv _hb ihv ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i v' hv'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    cases pat with
    | var x =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letVar (ihv hv') (ihb hb')
    | wildcard =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
    | field _ =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
    | ref _ _ =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
    | tuple _ =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
    | array _ =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
    | or _ _ =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
    | pointer _ =>
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      exact .letWild (ihv hv') (ihb hb')
  | @«match» typ e scrut bs _hscrut _hcases _hcasesTyp ihscrut ihcases =>
    -- Delegate to the helper; passes the structural IHs for scrut and per-case bodies.
    exact termToConcrete_match_arm_preserves_TypesNotFunction typ e scrut bs
      (fun {cs} hcs => ihscrut hcs)
      (fun pc hpc {cb} hcb => ihcases pc hpc hcb)
      _hrun
  | @app typ e g tArgs args u _hargs ih =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i args' hargs'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    refine .app ?_
    intro a ha
    exact List.mem_mapM_ok_forall
      (P := fun x => x ∈ args) (Q := Concrete.Term.TypesNotFunction cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) args args' (fun x hx => hx) hargs' a ha
  | @add typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .add (iha ha') (ihb hb')
  | @sub typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .sub (iha ha') (ihb hb')
  | @mul typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .mul (iha ha') (ihb hb')
  | @eqZero typ e a _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .eqZero (iha ha')
  | @proj typ e a n _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .proj (iha ha')
  | @get typ e a n _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .get (iha ha')
  | @slice typ e a i j _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .slice (iha ha')
  | @«set» typ e a n v _ _ iha ihv =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i v' hv'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .set (iha ha') (ihv hv')
  | @store typ e a _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .store (iha ha')
  | @load typ e a _htyp haty ha iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    -- Lift `Typ.FirstOrder a.typ` (haty, typed-side) to
    -- `Concrete.Typ.NotFunction a'.typ` via `typ_field_with_NF` (handles
    -- `.match` body shape using `hcasesTyp` from `TypesNotFunction.match`).
    have ha'_typ : typToConcrete mono a.typ = .ok a'.typ :=
      termToConcrete_typ_field_with_NF ha ha'
    have hNF : Concrete.Typ.NotFunction a'.typ :=
      typToConcrete_preserves_NotFunction haty ha'_typ
    exact .load hNF (iha ha')
  | @ptrVal typ e a _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ptrVal (iha ha')
  | @assertEq typ e a b r _ _ _ iha ihb ihr =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    split at _hrun
    · cases _hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .assertEq (iha ha') (ihb hb') (ihr hr')
  | @ioGetInfo typ e k _ ihk =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i k' hk'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ioGetInfo (ihk hk')
  | @ioSetInfo typ e k i l r _ _ _ _ ihk ihi ihl ihr =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i k' hk'
    split at _hrun
    · cases _hrun
    rename_i i' hi'
    split at _hrun
    · cases _hrun
    rename_i l' hl'
    split at _hrun
    · cases _hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ioSetInfo (ihk hk') (ihi hi') (ihl hl') (ihr hr')
  | @ioRead typ e i n _ ihi =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i i' hi'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ioRead (ihi hi')
  | @ioWrite typ e d r _ _ ihd ihr =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i d' hd'
    split at _hrun
    · cases _hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .ioWrite (ihd hd') (ihr hr')
  | @u8BitDecomposition typ e a _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8BitDecomposition (iha ha')
  | @u8ShiftLeft typ e a _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8ShiftLeft (iha ha')
  | @u8ShiftRight typ e a _ iha =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8ShiftRight (iha ha')
  | @u8Xor typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8Xor (iha ha') (ihb hb')
  | @u8Add typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8Add (iha ha') (ihb hb')
  | @u8Sub typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8Sub (iha ha') (ihb hb')
  | @u8And typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8And (iha ha') (ihb hb')
  | @u8Or typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8Or (iha ha') (ihb hb')
  | @u8LessThan typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u8LessThan (iha ha') (ihb hb')
  | @u32LessThan typ e a b _ _ iha ihb =>
    unfold termToConcrete at _hrun
    simp only [bind, Except.bind, pure, Except.pure] at _hrun
    split at _hrun
    · cases _hrun
    rename_i τ' _hτ
    split at _hrun
    · cases _hrun
    rename_i a' ha'
    split at _hrun
    · cases _hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at _hrun
    subst _hrun
    exact .u32LessThan (iha ha') (ihb hb')
  | @debug typ e label tOpt r ht hr iht ihr =>
    cases htmatch : tOpt with
    | none =>
      rw [htmatch] at _hrun
      unfold termToConcrete at _hrun
      simp only [bind, Except.bind, pure, Except.pure] at _hrun
      split at _hrun
      · cases _hrun
      rename_i τ' _hτ
      split at _hrun
      · cases _hrun
      rename_i r' hr'
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      refine .debug ?_ (ihr hr')
      intro tval htval; cases htval
    | some sub =>
      rw [htmatch] at _hrun
      unfold termToConcrete at _hrun
      simp only [bind, Except.bind, pure, Except.pure] at _hrun
      split at _hrun
      · cases _hrun
      rename_i sub' hsub'
      split at _hrun
      · cases _hrun
      rename_i τ' _hτ
      split at _hrun
      · cases _hrun
      rename_i r' hr'
      simp only [Except.ok.injEq] at _hrun
      subst _hrun
      refine .debug ?_ (ihr hr')
      intro tval htval
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub htmatch hsub'

/-! ### `step4Lower` fold: typed-side → concrete-side `TypesNotFunction`.

Mirrors `step4Lower_fold_preserves_TermRefsDt` (F=0 in `Shapes.lean`),
delegating per-body to `termToConcrete_preserves_TypesNotFunction`. -/

theorem step4Lower_fold_preserves_TypesNotFunction
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmdNF : Typed.Decls.TypesNotFunction monoDecls)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    Concrete.Decls.TypesNotFunction concDecls := by
  intro g cf hcf_get
  obtain ⟨f, hmd_get, hbody_eq⟩ :=
    step4Lower_fold_function_origin hcf_get hfold
  have hbody_typed : Typed.Term.TypesNotFunction f.body := hmdNF g f hmd_get
  exact termToConcrete_preserves_TypesNotFunction (cd := concDecls) hbody_typed hbody_eq

/-- **Top-level: `concretize` preserves `TypesNotFunction` from typed to concrete.**

Under `NoTypesAreFunctions t` (every typed `.load` carrier type is `Typ.FirstOrder`),
every concrete function body in `cd` has its `.letLoad`/`.load` carrier types
free of `.function` leaves.

Composition mirror of `concretize_preserves_TermRefsDt`:
1. **Drain** (F=0 modulo `concretize_PendingArgsFO_bridge`):
   `NewFunctionsTypesNotFunction` survives the worklist drain.
2. **`concretizeBuild`** (currently sorry, mirrors E.5): typed-side
   `TypesNotFunction` survives the 3-fold over `monoDecls`.
3. **`step4Lower` fold** (F=0 modulo `termToConcrete_preserves_TypesNotFunction`):
   typed-side → concrete-side. -/
theorem concretize_preserves_TypesNotFunction
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hsrc : NoTypesAreFunctions t)
    (hARFO_src : NoPolyAppRefTArgs t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.TypesNotFunction cd := by
  have htdsNF : Typed.Decls.TypesNotFunction tds := hsrc tds hts
  have hARFO : Typed.Decls.AppRefTArgsFO tds := hARFO_src tds hts
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · rename_i err _; cases hconc
  rename_i drained hdrain
  -- Stage 2: drain produces newFunctions all of which satisfy
  -- `Typed.Term.TypesNotFunction`. Threads `PendingArgsFO` companion via
  -- `concretize_PendingArgsFO_bridge`.
  have hinit : DrainState.NewFunctionsTypesNotFunction
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } :=
    DrainState.NewFunctionsTypesNotFunction.init _
  have hpargs_init : DrainState.PendingArgsFO
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } :=
    (concretize_PendingArgsFO_bridge tds hARFO).1
  have hpargs_chain : ∀ s s', DrainState.PendingArgsFO s →
      concretizeDrainIter tds s = .ok s' → DrainState.PendingArgsFO s' :=
    (concretize_PendingArgsFO_bridge tds hARFO).2
  have hnfNF : ∀ f ∈ drained.newFunctions, Typed.Term.TypesNotFunction f.body :=
    concretize_drain_preserves_NewFunctionsTypesNotFunction htdsNF
      _ _ hinit hpargs_init hpargs_chain hdrain
  -- Stage 3: concretizeBuild preserves typed-side TypesNotFunction.
  have hmdNF : Typed.Decls.TypesNotFunction
      (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes) :=
    concretizeBuild_preserves_TypesNotFunction htdsNF hnfNF
  -- Stage 4: step4Lower fold lifts to concrete-side.
  exact step4Lower_fold_preserves_TypesNotFunction hmdNF hconc

end Aiur

end -- @[expose] public section
