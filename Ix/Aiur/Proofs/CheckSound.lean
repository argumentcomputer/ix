module
public import Ix.Aiur.Compiler.Simple
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.TypedInvariants

/-!
Checker soundness.

**Required, not optional.** Without this, `Lower.preservation` has a hole:
"type annotations are accurate" is an unjustified assumption, and the claim
that Lower preserves semantics cannot be discharged.

If intrinsic typing is adopted, this theorem vanishes because well-typedness
becomes structural.
-/

public section

namespace Aiur

open Source

-- `ValueShapeMatches` + `WellFormedEnv` + `checkAndSimplify_sound` DELETED:
-- orphan speculative infra. `checkAndSimplify_sound` is a 40-arm per-case
-- structural induction claiming "every type annotation matches what the
-- reference evaluator produces". Never consumed — `Lower.preservation`'s
-- current signature uses `typFlatSize`/`typSize` invariants directly, not
-- shape-matching. Reintroduce when `Lower.preservation`'s proof actually
-- needs the shape-matching claim (likely when intrinsic typing is adopted,
-- which would eliminate this theorem entirely). See `Semantics/Relation.lean`
-- docstring for downstream commentary.

/-! ### `checkAndSimplify_preserves_inputs` family

`checkFunction` returns `⟨function.name, function.params, function.inputs,
function.output, body, function.entry⟩` — `.inputs` is untouched. And
`simplifyDecls` inserts `{ f with body := body' }` — `.inputs` untouched.
So for every shared function name, `tf.inputs = f.inputs`, and the two
flat-size sums are trivially equal.

Three-layer proof: invariant `FnMatchP` oriented typed→source (kind
preservation + inputs equality on functions). Preserved by the typecheck
fold (each source entry inserts a matching typed entry) and by
`simplifyDecls` (body rewrite doesn't touch inputs). The existence claim
additionally needs key-set preservation, proved inline as
`checkAndSimplify_keys_local` (duplicated from the private lemma in
`CompilerPreservation.lean` to avoid an import cycle). -/

/-- Single invariant combining kind-preservation and input-preservation,
oriented from typed-side to source-side. -/
@[expose] def FnMatchP (d : Source.Decls) (td : Typed.Decls) : Prop :=
  ∀ k,
    (∀ tf, td.getByKey k = some (.function tf) →
      ∃ f, d.getByKey k = some (.function f) ∧ tf.inputs = f.inputs) ∧
    (∀ dt, td.getByKey k = some (.dataType dt) →
      d.getByKey k = some (.dataType dt)) ∧
    (∀ dt c, td.getByKey k = some (.constructor dt c) →
      d.getByKey k = some (.constructor dt c))

private theorem FnMatchP_default (d : Source.Decls) :
    FnMatchP d (default : Typed.Decls) := by
  intro k
  have hnone : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro tf hget; rw [hnone] at hget; cases hget
  · intro dt hget; rw [hnone] at hget; cases hget
  · intro dt c hget; rw [hnone] at hget; cases hget

/-- `checkFunction` preserves `.inputs`. -/
private theorem checkFunction_inner_preserves_inputs
    (function : Function) (ctx : CheckContext) (s : CheckState)
    {f' : Typed.Function} {s' : CheckState}
    (h : checkFunction function ctx s = .ok (f', s')) :
    f'.inputs = function.inputs := by
  unfold checkFunction at h
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
             StateT.pure, Except.pure] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i inferOut _hinfer
  split at h
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hfeq, _⟩ := h
    rw [← hfeq]
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    split at h
    · rename_i _
      simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
                 StateT.pure, Except.pure] at h
      split at h
      · exact absurd h (by intro h'; cases h')
      rename_i _ _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hfeq, _⟩ := h
      rw [← hfeq]
    · rename_i _
      exact absurd h (by intro h'; cases h')

/-- `.run'`-form of `checkFunction` preserves `.inputs`. -/
private theorem checkFunction_run'_preserves_inputs
    (function : Function) (ctx : CheckContext)
    {f' : Typed.Function}
    (h : ((checkFunction function) ctx).run' {} = .ok f') :
    f'.inputs = function.inputs := by
  unfold StateT.run' at h
  simp only [Functor.map, Except.map] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i pair hpair
  simp only [Except.ok.injEq] at h
  obtain ⟨f_res, s_res⟩ := pair
  simp only at h
  subst h
  exact checkFunction_inner_preserves_inputs function ctx _ hpair

/-- `checkAndSimplify`'s first (typecheck) fold preserves `FnMatchP`. -/
private theorem FnMatchP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    FnMatchP decls typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact FnMatchP_default decls
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_src : decls.getByKey name = some decl :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro d' c' hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
          obtain ⟨heq1, heq2⟩ := hget
          subst heq1; subst heq2
          exact hname_src
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).1 tf hget
        · intro dt hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.1 dt hget
        · intro dt c' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.2 dt c' hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          subst hget
          exact hname_src
        · intro dt c hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).1 tf hget
        · intro dt hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.1 dt hget
        · intro dt c' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.2 dt c' hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hf'inputs : f'.inputs = f.inputs :=
        checkFunction_run'_preserves_inputs f (getFunctionContext f decls) hf'
      intro k
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
          subst hget
          refine ⟨f, hname_src, ?_⟩
          exact hf'inputs
        · intro dt hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt c hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).1 tf hget
        · intro dt hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.1 dt hget
        · intro dt c' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.2 dt c' hget

/-- `simplifyDecls` preserves `FnMatchP`. -/
private theorem FnMatchP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : FnMatchP decls typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    FnMatchP decls typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact FnMatchP_default decls
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_td : typedDecls.getByKey name = some d :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hfmatch : ∃ fsrc, decls.getByKey name = some (.function fsrc) ∧
                             f.inputs = fsrc.inputs :=
        (hP name).1 f hname_td
      intro k
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
          subst hget
          obtain ⟨fsrc, hfsrc, hinputs⟩ := hfmatch
          refine ⟨fsrc, hfsrc, ?_⟩
          exact hinputs
        · intro dt hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt c hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).1 tf hget
        · intro dt hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.1 dt hget
        · intro dt c' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.2 dt c' hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hdmatch : decls.getByKey name = some (.dataType dt) :=
        (hP name).2.1 dt hname_td
      intro k
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt' hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          subst hget
          exact hdmatch
        · intro dt' c hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).1 tf hget
        · intro dt' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.1 dt' hget
        · intro dt' c' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.2 dt' c' hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hcmatch : decls.getByKey name = some (.constructor dt c) :=
        (hP name).2.2 dt c hname_td
      intro k
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt' hget; rw [IndexMap.getByKey_insert_self] at hget; cases hget
        · intro dt' c' hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
          obtain ⟨heq1, heq2⟩ := hget
          subst heq1; subst heq2
          exact hcmatch
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        refine ⟨?_, ?_, ?_⟩
        · intro tf hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).1 tf hget
        · intro dt' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.1 dt' hget
        · intro dt' c' hget
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact (hPacc k).2.2 dt' c' hget

/-- Key-set preservation through `checkAndSimplify`. Duplicated from the
private lemma in `CompilerPreservation.lean` (avoids an import cycle since
`CompilerPreservation` imports `CheckSound`). -/
theorem checkAndSimplify_keys_local
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (_hdecls : t.mkDecls = .ok decls) (_hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g, decls.getByKey g ≠ none ↔ typedDecls.getByKey g ≠ none := by
  intro g
  rw [IndexMap.getByKey_ne_none_iff_containsKey, IndexMap.getByKey_ne_none_iff_containsKey]
  unfold Source.Toplevel.checkAndSimplify at _hts
  simp only [_hdecls, bind, Except.bind] at _hts
  rcases hwell : wellFormedDecls decls with _ | u
  · rw [hwell] at _hts; simp at _hts
  rw [hwell] at _hts
  simp only [pure, Except.pure] at _hts
  split at _hts
  · simp at _hts
  rename_i _ td htc_gen
  unfold simplifyDecls at _hts
  simp only [bind, Except.bind, pure, Except.pure] at _hts
  have hsp_gen := _hts
  have hfold_ck : td.containsKey g ↔
      ∃ p ∈ decls.pairs.toList, (p.1 == g) = true := by
    refine IndexMap.indexMap_foldlM_insertKey_default_iff decls _ ?_ g td htc_gen
    intro acc x r hr g'
    cases hd : x.snd with
    | constructor d c =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | dataType d =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | function f =>
      simp only [hd] at hr
      rcases hf : ((checkFunction f) (getFunctionContext f decls)).run' {} with err | tf
      · rw [hf] at hr; simp at hr
      · rw [hf] at hr
        simp only [Except.ok.injEq] at hr
        subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
  have hsimp_ck : typedDecls.containsKey g ↔
      ∃ p ∈ td.pairs.toList, (p.1 == g) = true := by
    refine IndexMap.indexMap_foldlM_insertKey_default_iff td _ ?_ g typedDecls hsp_gen
    intro acc x r hr g'
    cases hd : x.snd with
    | function f =>
      simp only [hd] at hr
      rcases hb : simplifyTypedTerm decls f.body with err | v
      · rw [hb] at hr; simp at hr
      · rw [hb] at hr
        simp only [Except.ok.injEq] at hr
        subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | dataType dt =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | constructor dt c =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
  rw [IndexMap.containsKey_iff_exists_pair decls g, ← hfold_ck,
      IndexMap.containsKey_iff_exists_pair td g, ← hsimp_ck]

/-- Master invariant: `FnMatchP` holds between `decls` (mkDecls output) and
`typedDecls` (checkAndSimplify output). -/
theorem FnMatchP_checkAndSimplify
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    FnMatchP decls typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hMid := FnMatchP_of_checkFold hfold
  exact FnMatchP_of_simplifyDecls hMid hts

/-- `checkAndSimplify` preserves each shared function's `.inputs` list. -/
theorem checkAndSimplify_preserves_inputs
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    tf.inputs = f.inputs := by
  have hP := FnMatchP_checkAndSimplify hdecls hts
  obtain ⟨fsrc, hfsrc, hinputs⟩ := (hP name).1 tf htyped
  rw [hsrc] at hfsrc
  simp only [Option.some.injEq, Source.Declaration.function.injEq] at hfsrc
  subst hfsrc
  exact hinputs

/-- `checkAndSimplify` preserves the function-input flat-size sum on each
shared function entry. Trivial consequence of
`checkAndSimplify_preserves_inputs`. -/
theorem checkAndSimplify_preserves_input_flat_sum
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    (f.inputs.map Prod.snd).foldl
        (fun acc t => acc + typFlatSize decls {} t) 0 =
      (tf.inputs.map Prod.snd).foldl
        (fun acc t => acc + typFlatSize decls {} t) 0 := by
  rw [checkAndSimplify_preserves_inputs hdecls hts hsrc htyped]

/-- `checkAndSimplify` extractor: lifts a source-function entry to a typed-function
entry preserving input flat-size sum. -/
theorem checkAndSimplify_extract_typed_function
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function}
    (hsrc : decls.getByKey name = some (.function f)) :
    ∃ tf : Typed.Function,
      typedDecls.getByKey name = some (.function tf) ∧
      (f.inputs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) 0 =
        (tf.inputs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) 0 := by
  have hkeys := checkAndSimplify_keys_local hdecls hts name
  have hsrc_ne : decls.getByKey name ≠ none := by rw [hsrc]; simp
  have htd_ne : typedDecls.getByKey name ≠ none := hkeys.mp hsrc_ne
  have hP := FnMatchP_checkAndSimplify hdecls hts
  match htd : typedDecls.getByKey name with
  | none => exact absurd htd htd_ne
  | some (.function tf) =>
    refine ⟨tf, rfl, ?_⟩
    rw [checkAndSimplify_preserves_inputs hdecls hts hsrc htd]
  | some (.dataType dt) =>
    exfalso
    have := (hP name).2.1 dt htd
    rw [hsrc] at this
    cases this
  | some (.constructor dt c) =>
    exfalso
    have := (hP name).2.2 dt c htd
    rw [hsrc] at this
    cases this

/-! ### `checkAndSimplify_preserves_params` family

Mirrors the `checkAndSimplify_preserves_inputs` chain above for `.params`
instead of `.inputs`, plus a source-side invariant `SrcFnParamsMonoP`
specific to `FullyMonomorphic` programs. Used in `StructCompatible.lean`
to derive `tf.params.isEmpty = true` for the `htf_mono` bridge. -/

/-- Every function entry in source decls has empty params. -/
private def SrcFnParamsMonoP (d : Source.Decls) : Prop :=
  ∀ k f, d.getByKey k = some (.function f) → f.params = []

private theorem SrcFnParamsMonoP_default :
    SrcFnParamsMonoP (default : Source.Decls) := by
  intro k f hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem SrcFnParamsMonoP_insert_dataType
    {d : Source.Decls} (hP : SrcFnParamsMonoP d) (name : Global) (dt : DataType) :
    SrcFnParamsMonoP (d.insert name (.dataType dt)) := by
  intro k f hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k f hget

private theorem SrcFnParamsMonoP_insert_constructor
    {d : Source.Decls} (hP : SrcFnParamsMonoP d) (name : Global)
    (dt : DataType) (c : Constructor) :
    SrcFnParamsMonoP (d.insert name (.constructor dt c)) := by
  intro k f hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k f hget

/-- `mkDecls_functionStep` preserves `SrcFnParamsMonoP` when inserted function
has `params = []`. -/
private theorem SrcFnParamsMonoP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcFnParamsMonoP acc.2) (hmono : function.params = [])
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SrcFnParamsMonoP acc'.2 := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  intro k f hget
  by_cases hkn : (function.name == k) = true
  · have hkEq : function.name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    simp only at hget
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.function.injEq] at hget
    rw [← hget]
    exact hmono
  · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    simp only at hget
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k f hget

/-- Inner ctor fold of `mkDecls_dataTypeStep` preserves `SrcFnParamsMonoP`. -/
private theorem SrcFnParamsMonoP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SrcFnParamsMonoP init.2 →
      ctors.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SrcFnParamsMonoP result.2 := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hP hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro init result hP hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hc
    split at hc
    · exact absurd hc (by intro h; cases h)
    · simp only [Except.ok.injEq] at hc
      subst hc
      apply ih _ result _ hfold
      exact SrcFnParamsMonoP_insert_constructor hP _ _ _

/-- `mkDecls_dataTypeStep` preserves `SrcFnParamsMonoP`. -/
private theorem SrcFnParamsMonoP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcFnParamsMonoP acc.2)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SrcFnParamsMonoP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hP_mid : SrcFnParamsMonoP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    SrcFnParamsMonoP_insert_dataType hP dataType.name _
  exact SrcFnParamsMonoP_ctor_fold dataType.name { dataType with constructors }
    constructors _ acc' hP_mid hstep

/-- Under `FullyMonomorphic t`, `mkDecls` produces a `Source.Decls` where every
function entry has empty `params`. -/
private theorem SrcFnParamsMonoP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (hmono : FullyMonomorphic toplevel)
    (h : toplevel.mkDecls = .ok decls) :
    SrcFnParamsMonoP decls := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : SrcFnParamsMonoP afterFns.2 := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · show SrcFnParamsMonoP (aliasNames, (default : Source.Decls)).2
      exact SrcFnParamsMonoP_default
    · intro a x a' hmem hstep hP
      have hxmono : x.params = [] :=
        hmono.1 x (Array.mem_toList_iff.mp hmem)
      exact SrcFnParamsMonoP_functionStep hP hxmono hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' _hmem hstep hP
    exact SrcFnParamsMonoP_dataTypeStep hP hstep

/-- Typed-side invariant oriented typed→source carrying params equality. -/
private def TdFnParamsMatchP (d : Source.Decls) (td : Typed.Decls) : Prop :=
  ∀ k tf, td.getByKey k = some (.function tf) →
    ∃ f, d.getByKey k = some (.function f) ∧ tf.params = f.params

private theorem TdFnParamsMatchP_default (d : Source.Decls) :
    TdFnParamsMatchP d (default : Typed.Decls) := by
  intro k tf hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

/-- `checkFunction`'s inner form preserves `.params`. -/
private theorem checkFunction_inner_preserves_params
    (function : Function) (ctx : CheckContext) (s : CheckState)
    {f' : Typed.Function} {s' : CheckState}
    (h : checkFunction function ctx s = .ok (f', s')) :
    f'.params = function.params := by
  unfold checkFunction at h
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
             StateT.pure, Except.pure] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i inferOut _hinfer
  split at h
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hfeq, _⟩ := h
    rw [← hfeq]
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    split at h
    · rename_i _
      simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
                 StateT.pure, Except.pure] at h
      split at h
      · exact absurd h (by intro h'; cases h')
      rename_i _ _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hfeq, _⟩ := h
      rw [← hfeq]
    · rename_i _
      exact absurd h (by intro h'; cases h')

/-- `.run'`-form of `checkFunction` preserves `.params`. -/
private theorem checkFunction_run'_preserves_params
    (function : Function) (ctx : CheckContext)
    {f' : Typed.Function}
    (h : ((checkFunction function) ctx).run' {} = .ok f') :
    f'.params = function.params := by
  unfold StateT.run' at h
  simp only [Functor.map, Except.map] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i pair hpair
  simp only [Except.ok.injEq] at h
  obtain ⟨f_res, s_res⟩ := pair
  simp only at h
  subst h
  exact checkFunction_inner_preserves_params function ctx _ hpair

/-- The typecheck fold of `checkAndSimplify` preserves `TdFnParamsMatchP`. -/
private theorem TdFnParamsMatchP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TdFnParamsMatchP decls typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TdFnParamsMatchP_default decls
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_src : decls.getByKey name = some decl :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hf'params : f'.params = f.params :=
        checkFunction_run'_preserves_params f (getFunctionContext f decls) hf'
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        subst hget
        refine ⟨f, hname_src, ?_⟩
        exact hf'params
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget

/-- `simplifyDecls` preserves `TdFnParamsMatchP`. -/
private theorem TdFnParamsMatchP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TdFnParamsMatchP decls typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TdFnParamsMatchP decls typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TdFnParamsMatchP_default decls
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_td : typedDecls.getByKey name = some d :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hfmatch : ∃ fsrc, decls.getByKey name = some (.function fsrc) ∧
                             f.params = fsrc.params :=
        hP name f hname_td
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        subst hget
        obtain ⟨fsrc, hfsrc, hparams⟩ := hfmatch
        refine ⟨fsrc, hfsrc, ?_⟩
        exact hparams
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget

/-- Master invariant: `TdFnParamsMatchP` holds between `decls` and `typedDecls`. -/
private theorem TdFnParamsMatchP_checkAndSimplify
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    TdFnParamsMatchP decls typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hMid := TdFnParamsMatchP_of_checkFold hfold
  exact TdFnParamsMatchP_of_simplifyDecls hMid hts

/-- `checkAndSimplify` preserves each shared function's `.params` list. -/
theorem checkAndSimplify_preserves_params
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    tf.params = f.params := by
  have hP := TdFnParamsMatchP_checkAndSimplify hdecls hts
  obtain ⟨fsrc, hfsrc, hparams⟩ := hP name tf htyped
  rw [hsrc] at hfsrc
  simp only [Option.some.injEq, Source.Declaration.function.injEq] at hfsrc
  subst hfsrc
  exact hparams

/-- The `htf_mono` bridge. Combines `SrcFnParamsMonoP_mkDecls` +
`checkAndSimplify_preserves_params` to derive `tf.params = []`, hence
`tf.params.isEmpty = true`. -/
theorem htf_mono_bridge
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    tf.params.isEmpty = true := by
  have hsrc_mono : f.params = [] :=
    SrcFnParamsMonoP_mkDecls hmono hdecls name f hsrc
  have hpreserve : tf.params = f.params :=
    checkAndSimplify_preserves_params hdecls hts hsrc htyped
  rw [hpreserve, hsrc_mono]
  rfl

/-- Typed-side version of `FullyMonomorphic`: every typed function in
`typedDecls` has `params = []`. Derived from `FullyMonomorphic t` via
`TdFnParamsMatchP_checkAndSimplify` + `SrcFnParamsMonoP_mkDecls`. -/
theorem typedDecls_params_empty_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g tf, typedDecls.getByKey g = some (.function tf) → tf.params = [] := by
  intro g tf htyped
  have hP := TdFnParamsMatchP_checkAndSimplify hdecls hts
  obtain ⟨f, hfsrc, hparams⟩ := hP g tf htyped
  have hsrc_mono : f.params = [] :=
    SrcFnParamsMonoP_mkDecls hmono hdecls g f hfsrc
  rw [hparams, hsrc_mono]

/-! ## Source-side invariant: every datatype entry has empty params.

Mirror of `SrcFnParamsMonoP` family for datatype entries. Under
`FullyMonomorphic t`, `t.mkDecls` produces a `Source.Decls` where every
`.dataType dt` entry satisfies `dt.params = []`. -/

@[expose] def SrcDtParamsMonoP (d : Source.Decls) : Prop :=
  ∀ k dt, d.getByKey k = some (.dataType dt) → dt.params = []

private theorem SrcDtParamsMonoP_default :
    SrcDtParamsMonoP (default : Source.Decls) := by
  intro k dt hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem SrcDtParamsMonoP_insert_function
    {d : Source.Decls} (hP : SrcDtParamsMonoP d) (name : Global)
    (f : Source.Function) :
    SrcDtParamsMonoP (d.insert name (.function f)) := by
  intro k dt hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt hget

private theorem SrcDtParamsMonoP_insert_constructor
    {d : Source.Decls} (hP : SrcDtParamsMonoP d) (name : Global)
    (dt : DataType) (c : Constructor) :
    SrcDtParamsMonoP (d.insert name (.constructor dt c)) := by
  intro k dt' hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' hget

private theorem SrcDtParamsMonoP_insert_dataType
    {d : Source.Decls} (hP : SrcDtParamsMonoP d) (name : Global) (dt : DataType)
    (hmono : dt.params = []) :
    SrcDtParamsMonoP (d.insert name (.dataType dt)) := by
  intro k dt' hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hget
    rw [← hget]
    exact hmono
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' hget

private theorem SrcDtParamsMonoP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Source.Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcDtParamsMonoP acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SrcDtParamsMonoP acc'.2 := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  simp only
  exact SrcDtParamsMonoP_insert_function hP _ _

private theorem SrcDtParamsMonoP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SrcDtParamsMonoP init.2 →
      ctors.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SrcDtParamsMonoP result.2 := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hP hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro init result hP hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hc
    split at hc
    · exact absurd hc (by intro h; cases h)
    · simp only [Except.ok.injEq] at hc
      subst hc
      apply ih _ result _ hfold
      exact SrcDtParamsMonoP_insert_constructor hP _ _ _

private theorem SrcDtParamsMonoP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcDtParamsMonoP acc.2) (hmono : dataType.params = [])
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SrcDtParamsMonoP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hparams' : ({ dataType with constructors } : DataType).params = [] := hmono
  have hP_mid : SrcDtParamsMonoP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    SrcDtParamsMonoP_insert_dataType hP dataType.name _ hparams'
  exact SrcDtParamsMonoP_ctor_fold dataType.name { dataType with constructors }
    constructors _ acc' hP_mid hstep

theorem SrcDtParamsMonoP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (hmono : FullyMonomorphic toplevel)
    (h : toplevel.mkDecls = .ok decls) :
    SrcDtParamsMonoP decls := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : SrcDtParamsMonoP afterFns.2 := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · show SrcDtParamsMonoP (aliasNames, (default : Source.Decls)).2
      exact SrcDtParamsMonoP_default
    · intro a x a' _hmem hstep hP
      exact SrcDtParamsMonoP_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' hmem hstep hP
    have hxmono : x.params = [] :=
      hmono.2 x (Array.mem_toList_iff.mp hmem)
    exact SrcDtParamsMonoP_dataTypeStep hP hxmono hstep

/-! ## Typed-side invariant: every typed dataType entry matches a source
dataType entry at the same key. -/

@[expose] def TdDtParamsMatchP (d : Source.Decls) (td : Typed.Decls) : Prop :=
  ∀ k dt, td.getByKey k = some (.dataType dt) →
    d.getByKey k = some (.dataType dt)

private theorem TdDtParamsMatchP_default (d : Source.Decls) :
    TdDtParamsMatchP d (default : Typed.Decls) := by
  intro k dt hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem TdDtParamsMatchP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TdDtParamsMatchP decls typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TdDtParamsMatchP_default decls
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_src : decls.getByKey name = some decl :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
        subst hget
        exact hname_src
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' _hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget

private theorem TdDtParamsMatchP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TdDtParamsMatchP decls typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TdDtParamsMatchP decls typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TdDtParamsMatchP_default decls
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_td : typedDecls.getByKey name = some d :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hdmatch : decls.getByKey name = some (.dataType dt) :=
        hP name dt hname_td
      intro k dt' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
        subst hget
        exact hdmatch
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' hget

theorem TdDtParamsMatchP_checkAndSimplify
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    TdDtParamsMatchP decls typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hMid := TdDtParamsMatchP_of_checkFold hfold
  exact TdDtParamsMatchP_of_simplifyDecls hMid hts

/-- Datatype-side mirror of `typedDecls_params_empty_of_fullyMonomorphic`.
Derived from `FullyMonomorphic t` via `TdDtParamsMatchP_checkAndSimplify` +
`SrcDtParamsMonoP_mkDecls`. -/
theorem typedDecls_dt_params_empty_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g dt, typedDecls.getByKey g = some (.dataType dt) → dt.params = [] := by
  intro g dt htyped
  have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
  have hsrc : decls.getByKey g = some (.dataType dt) := hP g dt htyped
  have hmonoP := SrcDtParamsMonoP_mkDecls hmono hdecls
  exact hmonoP g dt hsrc

/-! ## Function-output preservation.

`checkFunction` returns `⟨name, params, inputs, output, body, entry, _⟩` — the
`output` field is copied through unchanged. And `simplifyDecls` inserts
`{ f with body := body' }`, not touching `output`. So for every function
`tf` in `typedDecls` matched by source function `f` at the same key, we have
`tf.output = f.output`. -/

/-- `checkFunction`'s inner form preserves `.output`. -/
private theorem checkFunction_inner_preserves_output
    (function : Function) (ctx : CheckContext) (s : CheckState)
    {f' : Typed.Function} {s' : CheckState}
    (h : checkFunction function ctx s = .ok (f', s')) :
    f'.output = function.output := by
  unfold checkFunction at h
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
             StateT.pure, Except.pure] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i inferOut _hinfer
  split at h
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hfeq, _⟩ := h
    rw [← hfeq]
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    split at h
    · rename_i _
      simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
                 StateT.pure, Except.pure] at h
      split at h
      · exact absurd h (by intro h'; cases h')
      rename_i _ _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hfeq, _⟩ := h
      rw [← hfeq]
    · rename_i _
      exact absurd h (by intro h'; cases h')

/-- `.run'`-form of `checkFunction` preserves `.output`. -/
private theorem checkFunction_run'_preserves_output
    (function : Function) (ctx : CheckContext)
    {f' : Typed.Function}
    (h : ((checkFunction function) ctx).run' {} = .ok f') :
    f'.output = function.output := by
  unfold StateT.run' at h
  simp only [Functor.map, Except.map] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i pair hpair
  simp only [Except.ok.injEq] at h
  obtain ⟨f_res, s_res⟩ := pair
  simp only at h
  subst h
  exact checkFunction_inner_preserves_output function ctx _ hpair

/-- Kind-preservation + output-preservation on functions, typed→source. -/
private def FnOutputMatchP (d : Source.Decls) (td : Typed.Decls) : Prop :=
  ∀ k tf, td.getByKey k = some (.function tf) →
    ∃ f, d.getByKey k = some (.function f) ∧ tf.output = f.output

private theorem FnOutputMatchP_default (d : Source.Decls) :
    FnOutputMatchP d (default : Typed.Decls) := by
  intro k tf hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem FnOutputMatchP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    FnOutputMatchP decls typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact FnOutputMatchP_default decls
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_src : decls.getByKey name = some decl :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hf'output : f'.output = f.output :=
        checkFunction_run'_preserves_output f (getFunctionContext f decls) hf'
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        subst hget
        exact ⟨f, hname_src, hf'output⟩
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget

private theorem FnOutputMatchP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : FnOutputMatchP decls typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    FnOutputMatchP decls typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact FnOutputMatchP_default decls
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_td : typedDecls.getByKey name = some d :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      -- For the new function entry `{ f with body := body' }` at `name`:
      -- extract source match from the outer invariant `hP` on typedDecls
      -- (rather than the mid-state `hPacc`).
      obtain ⟨fsrc, hfsrc, houtput⟩ := hP name f hname_td
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        subst hget
        -- tf = { f with body := body' }; .output field unchanged.
        exact ⟨fsrc, hfsrc, houtput⟩
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget; cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget

private theorem FnOutputMatchP_checkAndSimplify
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    FnOutputMatchP decls typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hMid := FnOutputMatchP_of_checkFold hfold
  exact FnOutputMatchP_of_simplifyDecls hMid hts

/-- `checkAndSimplify` preserves each function's `.output` type. -/
theorem checkAndSimplify_preserves_output
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf)) :
    tf.output = f.output := by
  have hP := FnOutputMatchP_checkAndSimplify hdecls hts
  obtain ⟨fsrc, hfsrc, houtput⟩ := hP name tf htyped
  rw [hsrc] at hfsrc
  simp only [Option.some.injEq, Source.Declaration.function.injEq] at hfsrc
  subst hfsrc
  exact houtput

/-! ## Source-to-typed dt-key preservation.

Forward direction: every `.dataType`-keyed entry in `decls` survives through
`checkAndSimplify` to `typedDecls` at the same key, as a `.dataType`. Derived
from the reverse invariant `FnMatchP` + key-set equivalence
`checkAndSimplify_keys_local`: typed `.function`/`.constructor` at key g would
imply source `.function`/`.constructor` at g (contradicting source being
`.dataType`), so typed must also be `.dataType`. -/

/-- Forward bridge: for every `.dataType`-at-key-g in source decls, there is
some `.dataType`-at-key-g in typed decls. The typed-side dt is not required
to match the source-side dt value — callers that need value equality use
`TdDtParamsMatchP` on top to recover `decls.getByKey g = some (.dataType dt)`
(upon which `dt` on both sides is shown to match). -/
theorem checkAndSimplify_src_dt_to_td
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {g : Global} {dt : DataType}
    (hg : decls.getByKey g = some (.dataType dt)) :
    ∃ dt', typedDecls.getByKey g = some (.dataType dt') := by
  have hkeys := checkAndSimplify_keys_local hdecls hts g
  have hsrc_ne : decls.getByKey g ≠ none := by rw [hg]; simp
  have htd_ne : typedDecls.getByKey g ≠ none := hkeys.mp hsrc_ne
  have hP := FnMatchP_checkAndSimplify hdecls hts
  match htd : typedDecls.getByKey g with
  | none => exact absurd htd htd_ne
  | some (.function tf) =>
    exfalso
    obtain ⟨f, hfsrc, _⟩ := (hP g).1 tf htd
    rw [hg] at hfsrc; cases hfsrc
  | some (.dataType dt') =>
    exact ⟨dt', rfl⟩
  | some (.constructor dt' c) =>
    exfalso
    have := (hP g).2.2 dt' c htd
    rw [hg] at this; cases this

/-! ## Source-side well-formedness reflection.

Given `wellFormedDecls decls = .ok ()`, we can derive structural well-
formedness of every type annotation in every declaration: every `.ref g`/
`.app g _` appearing at a checker-visible position has `decls.getByKey g =
some (.dataType dt)` with `dt.params = []` (for `.ref`) or matching arity
(for `.app`, which under `FullyMonomorphic` also has empty params).

The helper `wellFormedDecls.wellFormedType` is defined as a `where`-bound
helper inside `wellFormedDecls`. We reference it via its dotted name. -/

/-- Source-side counterpart to `TypRefsAreDtKeys`: every `.ref g`/`.app g _`
in structurally-inspected positions has `decls.getByKey g = some (.dataType dt)`
with `dt.params = []`. `.function` / `.mvar` are leaves (checker does not
recurse). -/
inductive SrcTypRefsAreDtKeys (decls : Source.Decls) : Typ → Prop
  | unit    : SrcTypRefsAreDtKeys decls .unit
  | field   : SrcTypRefsAreDtKeys decls .field
  | mvar n  : SrcTypRefsAreDtKeys decls (.mvar n)
  | func {ins out}
      (hi : ∀ t ∈ ins, SrcTypRefsAreDtKeys decls t)
      (ho : SrcTypRefsAreDtKeys decls out) :
      SrcTypRefsAreDtKeys decls (.function ins out)
  | pointer {inner} (h : SrcTypRefsAreDtKeys decls inner) :
      SrcTypRefsAreDtKeys decls (.pointer inner)
  | tuple {ts} (h : ∀ t ∈ ts.toList, SrcTypRefsAreDtKeys decls t) :
      SrcTypRefsAreDtKeys decls (.tuple ts)
  | array {t n} (h : SrcTypRefsAreDtKeys decls t) :
      SrcTypRefsAreDtKeys decls (.array t n)
  | ref {g} (hdt : ∃ dt, decls.getByKey g = some (.dataType dt) ∧ dt.params = []) :
      SrcTypRefsAreDtKeys decls (.ref g)
  | app {g args}
      (hdt : ∃ dt, decls.getByKey g = some (.dataType dt) ∧
                   args.size = dt.params.length)
      (h : ∀ t ∈ args.toList, SrcTypRefsAreDtKeys decls t) :
      SrcTypRefsAreDtKeys decls (.app g args)

/-- Element-wise foldlM-to-Unit reflection: if a `foldlM` over `xs` in
`Except Unit` succeeds, every element's step succeeded (at some acc). -/
private theorem list_foldlM_unit_except_ok_elt
    {α ε : Type} {f : Unit → α → Except ε Unit}
    (xs : List α) (h : xs.foldlM f () = .ok ()) :
    ∀ x ∈ xs, f () x = .ok () := by
  induction xs with
  | nil => intros x hx; cases hx
  | cons hd tl ih =>
    intro x hx
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i v hd_ok
    -- v : Unit → must be ().
    cases v
    rcases List.mem_cons.mp hx with heq | hrest
    · subst heq; exact hd_ok
    · exact ih h x hrest

/-- Element-wise List.forM reflection. -/
private theorem list_forM_except_ok_elt
    {α ε : Type} {f : α → Except ε Unit} :
    ∀ (xs : List α), xs.forM f = .ok () → ∀ x ∈ xs, f x = .ok ()
  | [], _, x, hx => by cases hx
  | hd :: tl, h, x, hx => by
    -- `(hd :: tl).forM f = f hd >>= fun _ => tl.forM f`
    have hrw : (hd :: tl).forM f = f hd >>= fun _ => tl.forM f := rfl
    rw [hrw] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i v hd_ok
    cases v
    rcases List.mem_cons.mp hx with heq | hrest
    · subst heq; exact hd_ok
    · exact list_forM_except_ok_elt tl h x hrest

/-- `Array.forM` in `Except Unit` succeeded ⇒ each element's step OK. -/
private theorem array_forM_except_ok_elt
    {α ε : Type} {f : α → Except ε Unit}
    (xs : Array α) (h : xs.forM f = .ok ()) :
    ∀ x ∈ xs, f x = .ok () := by
  -- Array.forM unfolds to foldlM_eq_forM via (Array.forM f xs = xs.foldlM (fun _ a => f a) ()).
  have hrfl : xs.forM f = xs.foldlM (fun (_ : Unit) a => f a) () := rfl
  rw [hrfl] at h
  -- Convert to List.foldlM via Array.foldlM_toList.
  rw [← Array.foldlM_toList] at h
  intro x hx
  have hmem : x ∈ xs.toList := Array.mem_toList_iff.mpr hx
  exact list_foldlM_unit_except_ok_elt xs.toList h x hmem

/-- `List.attach.forM` in `Except Unit`: succeeded ⇒ each element OK. -/
private theorem list_attach_forM_except_ok_elt
    {α ε : Type} {xs : List α}
    {f : {x // x ∈ xs} → Except ε Unit}
    (h : xs.attach.forM f = .ok ()) :
    ∀ (x : α) (hx : x ∈ xs), f ⟨x, hx⟩ = .ok () := by
  intro x hx
  exact list_forM_except_ok_elt xs.attach h ⟨x, hx⟩ (List.mem_attach _ _)

/-- `Array.attach.forM` in `Except Unit`: succeeded ⇒ each element OK. -/
private theorem array_attach_forM_except_ok_elt
    {α ε : Type} {xs : Array α}
    {f : {x // x ∈ xs} → Except ε Unit}
    (h : xs.attach.forM f = .ok ()) :
    ∀ (x : α) (hx : x ∈ xs), f ⟨x, hx⟩ = .ok () := by
  intro x hx
  exact array_forM_except_ok_elt xs.attach h ⟨x, hx⟩ (Array.mem_attach _ _)

/-- Source-side reflection: if `wellFormedDecls.wellFormedType decls [] τ`
succeeds, then `SrcTypRefsAreDtKeys decls τ`. Structural induction over `τ`;
`.function` / `.mvar` / `.unit` / `.field` fall through unconditionally via
the `_ => .ok ()` tail in the checker. -/
theorem SrcTypRefsAreDtKeys_of_wellFormedType
    (decls : Source.Decls) :
    ∀ (τ : Typ),
      wellFormedDecls.wellFormedType decls [] τ = .ok () →
      SrcTypRefsAreDtKeys decls τ
  | .unit, _ => .unit
  | .field, _ => .field
  | .mvar n, _ => .mvar n
  | .function ins out, h => by
    unfold wellFormedDecls.wellFormedType at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hin
      refine .func ?_ ?_
      · intro t htmem
        have helt := list_attach_forM_except_ok_elt hin t htmem
        exact SrcTypRefsAreDtKeys_of_wellFormedType decls t helt
      · exact SrcTypRefsAreDtKeys_of_wellFormedType decls out h
  | .pointer inner, h => by
    unfold wellFormedDecls.wellFormedType at h
    exact .pointer (SrcTypRefsAreDtKeys_of_wellFormedType decls inner h)
  | .array t n, h => by
    unfold wellFormedDecls.wellFormedType at h
    exact .array (SrcTypRefsAreDtKeys_of_wellFormedType decls t h)
  | .ref g, h => by
    unfold wellFormedDecls.wellFormedType at h
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i dt hget
      split at h
      · rename_i hemp
        have hparams : dt.params = [] := List.isEmpty_iff.mp hemp
        exact .ref ⟨dt, hget, hparams⟩
      · exact absurd h (by intro h'; cases h')
    · exact absurd h (by intro h'; cases h')
    · exact absurd h (by intro h'; cases h')
  | .app g args, h => by
    unfold wellFormedDecls.wellFormedType at h
    split at h
    · rename_i dt hget
      simp only [bind, Except.bind] at h
      split at h
      · rename_i hsize
        have hsize_eq : args.size = dt.params.length := by
          have := beq_iff_eq.mp hsize
          exact this
        refine .app ⟨dt, hget, hsize_eq⟩ ?_
        intro t htmem
        have hmem : t ∈ args := Array.mem_toList_iff.mp htmem
        have helt := array_attach_forM_except_ok_elt h t hmem
        exact SrcTypRefsAreDtKeys_of_wellFormedType decls t helt
      · exact absurd h (by intro h'; cases h')
    · exact absurd h (by intro h'; cases h')
    · exact absurd h (by intro h'; cases h')
  | .tuple typs, h => by
    unfold wellFormedDecls.wellFormedType at h
    refine .tuple ?_
    intro t htmem
    have hmem : t ∈ typs := Array.mem_toList_iff.mp htmem
    have helt := array_attach_forM_except_ok_elt h t hmem
    exact SrcTypRefsAreDtKeys_of_wellFormedType decls t helt
  termination_by τ => sizeOf τ
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Reflect per-decl well-formedness: if `wellFormedDecls decls = .ok ()`,
every pair `(name, decl) ∈ decls.pairs.toList` is processed by `wellFormedDecl`
at some intermediate `visited` state. -/
private theorem wellFormedDecls_per_pair
    {decls : Source.Decls}
    (hwf : wellFormedDecls decls = .ok ()) :
    ∀ (name : Global) (decl : Source.Declaration),
      (name, decl) ∈ decls.pairs.toList →
      ∃ (visited : Std.HashSet Global) (visited' : Std.HashSet Global),
        wellFormedDecls.wellFormedDecl decls visited decl = .ok visited' := by
  unfold wellFormedDecls at hwf
  simp only [bind, Except.bind] at hwf
  split at hwf
  · exact absurd hwf (by intro h'; cases h')
  rename_i final hfold
  -- hfold : decls.pairs.foldlM (fun x y => wellFormedDecl x y.snd) default = .ok final
  rw [← Array.foldlM_toList] at hfold
  -- hfold now over decls.pairs.toList.
  intro name decl hmem
  have hstep := List.foldlM_except_witnesses
    (f := fun x y => wellFormedDecls.wellFormedDecl decls x y.snd)
    decls.pairs.toList _ _ hfold (name, decl) hmem
  exact hstep

/-- Reflect `wellFormedDecl`-at-source-dataType: every ctor-argtype of `dt` is
source-well-formed (via `wellFormedType [] t = .ok ()`). The visited
hashset is not consumed (we only care about the argtype well-formedness,
which the `.dataType` branch of `wellFormedDecl` ensures regardless of
whether `dt.name ∈ visited` — in the `visited`-contains case, the function
returns `.ok` without checking, but we also don't get the type claim; so
we require `¬ visited.contains dt.name`). -/
private theorem dataType_ctor_argtypes_wellFormed
    {decls : Source.Decls} {visited visited' : Std.HashSet Global}
    {dt : DataType}
    (hvis : visited.contains dt.name = false)
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.dataType dt) = .ok visited') :
    ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
      wellFormedDecls.wellFormedType decls dt.params t = .ok () := by
  unfold wellFormedDecls.wellFormedDecl at hstep
  simp only at hstep -- reduce .dataType match
  rw [hvis] at hstep
  simp only [Bool.not_false, ↓reduceIte] at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · exact absurd hstep (by intro h'; cases h')
  rename_i _params_val params_eq
  split at hstep
  · exact absurd hstep (by intro h'; cases h')
  rename_i _forM_val forM_eq
  intro c hcmem t htmem
  have helt := list_forM_except_ok_elt _ forM_eq t ?_
  · exact helt
  · rw [List.mem_flatMap]
    exact ⟨c, hcmem, htmem⟩

/-- Reflect `wellFormedDecl`-at-source-function: the output type + every
input type is well-formed under the function's params. -/
private theorem function_types_wellFormed
    {decls : Source.Decls} {visited visited' : Std.HashSet Global}
    {f : Source.Function}
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.function f) = .ok visited') :
    wellFormedDecls.wellFormedType decls f.params f.output = .ok () ∧
    ∀ lt ∈ f.inputs, wellFormedDecls.wellFormedType decls f.params lt.2 = .ok () := by
  unfold wellFormedDecls.wellFormedDecl at hstep
  simp only at hstep -- reduce .function match
  simp only [bind, Except.bind] at hstep
  -- Structure: checkUniqueParams >>= wellFormedType output >>= forM inputs.
  split at hstep
  · exact absurd hstep (by intro h'; cases h')
  rename_i _params_val _params_eq
  split at hstep
  · exact absurd hstep (by intro h'; cases h')
  rename_i _out_val output_eq
  split at hstep
  · exact absurd hstep (by intro h'; cases h')
  rename_i _forM_val forM_eq
  refine ⟨output_eq, ?_⟩
  intro lt hltmem
  exact list_forM_except_ok_elt _ forM_eq lt hltmem

/-- Reflect `wellFormedDecl`-at-source-constructor: always `.ok visited`,
no argtype checks happen here (handled in the dataType arm). -/
private theorem constructor_trivial_step
    {decls : Source.Decls} {visited visited' : Std.HashSet Global}
    {dt : DataType} {c : Constructor}
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.constructor dt c) = .ok visited') :
    visited' = visited := by
  unfold wellFormedDecls.wellFormedDecl at hstep
  simp only [pure, Except.pure, Except.ok.injEq] at hstep
  exact hstep.symm

/-! ## Public re-exports for use in `ConcretizeSound.lean`'s L1 proof. -/

/-- Typed `.dataType dt` at key g ⇒ source `.dataType dt` at key g (same dt). -/
theorem checkAndSimplify_dt_in_source
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {g : Global} {dt : DataType}
    (htyped : typedDecls.getByKey g = some (.dataType dt)) :
    decls.getByKey g = some (.dataType dt) :=
  TdDtParamsMatchP_checkAndSimplify hdecls hts g dt htyped

/-- Typed `.function tf` at key g ⇒ source `.function f` at key g + inputs eq. -/
theorem checkAndSimplify_fn_in_source
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {g : Global} {tf : Typed.Function}
    (htyped : typedDecls.getByKey g = some (.function tf)) :
    ∃ f, decls.getByKey g = some (.function f) ∧ tf.inputs = f.inputs :=
  (FnMatchP_checkAndSimplify hdecls hts g).1 tf htyped

/-- Typed `.constructor dt c` at key g ⇒ source `.constructor dt c` at key g. -/
theorem checkAndSimplify_ctor_in_source
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {g : Global} {dt : DataType} {c : Constructor}
    (htyped : typedDecls.getByKey g = some (.constructor dt c)) :
    decls.getByKey g = some (.constructor dt c) :=
  (FnMatchP_checkAndSimplify hdecls hts g).2.2 dt c htyped

/-- Source functions have `params = []` under `FullyMonomorphic`. -/
theorem mkDecls_fn_params_empty_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k f, decls.getByKey k = some (.function f) → f.params = [] :=
  SrcFnParamsMonoP_mkDecls hmono hdecls

/-- Source data types have `params = []` under `FullyMonomorphic`. -/
theorem mkDecls_dt_params_empty_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt, decls.getByKey k = some (.dataType dt) → dt.params = [] :=
  SrcDtParamsMonoP_mkDecls hmono hdecls

/-- `checkAndSimplify` success implies `wellFormedDecls` on the mkDecls output. -/
theorem checkAndSimplify_implies_wellFormedDecls
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    wellFormedDecls decls = .ok () := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i u hwf
  cases u
  exact hwf

/-! ## Public wrappers on the source-side well-formedness reflection. -/

/-- Per-pair well-formedness extraction: every source decl is processed by
`wellFormedDecl` at some intermediate visited state. -/
theorem wellFormedDecls_reflect_pair
    {decls : Source.Decls}
    (hwf : wellFormedDecls decls = .ok ())
    (name : Global) (decl : Source.Declaration)
    (hmem : (name, decl) ∈ decls.pairs.toList) :
    ∃ (visited : Std.HashSet Global) (visited' : Std.HashSet Global),
      wellFormedDecls.wellFormedDecl decls visited decl = .ok visited' :=
  wellFormedDecls_per_pair hwf name decl hmem

/-- Function-decl reflection: output + inputs well-formedness. -/
theorem wellFormedDecls_reflect_function
    {decls : Source.Decls} {visited visited' : Std.HashSet Global}
    {f : Source.Function}
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.function f) = .ok visited') :
    wellFormedDecls.wellFormedType decls f.params f.output = .ok () ∧
    ∀ lt ∈ f.inputs, wellFormedDecls.wellFormedType decls f.params lt.2 = .ok () :=
  function_types_wellFormed hstep

/-- DataType-decl reflection: ctor argtypes well-formedness (requires fresh
visited). -/
theorem wellFormedDecls_reflect_dataType
    {decls : Source.Decls} {visited visited' : Std.HashSet Global}
    {dt : DataType}
    (hvis : visited.contains dt.name = false)
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.dataType dt) = .ok visited') :
    ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
      wellFormedDecls.wellFormedType decls dt.params t = .ok () :=
  dataType_ctor_argtypes_wellFormed hvis hstep

/-! ## Key-is-name invariant for source datatype entries.

`mkDecls` inserts each `.dataType dt` entry at the key `dt.name` (see
`mkDecls_dataTypeStep`). Function and constructor inserts don't touch
dataType entries at other keys. Together this means: every `.dataType dt`
entry in the final `Source.Decls` has key = `dt.name`. -/

private def SrcDtKeyIsName (d : Source.Decls) : Prop :=
  ∀ k dt, d.getByKey k = some (.dataType dt) → k = dt.name

private theorem SrcDtKeyIsName_default :
    SrcDtKeyIsName (default : Source.Decls) := by
  intro k dt hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem SrcDtKeyIsName_insert_function
    {d : Source.Decls} (hP : SrcDtKeyIsName d) (name : Global)
    (f : Source.Function) :
    SrcDtKeyIsName (d.insert name (.function f)) := by
  intro k dt hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt hget

private theorem SrcDtKeyIsName_insert_constructor
    {d : Source.Decls} (hP : SrcDtKeyIsName d) (name : Global)
    (dt : DataType) (c : Constructor) :
    SrcDtKeyIsName (d.insert name (.constructor dt c)) := by
  intro k dt' hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' hget

private theorem SrcDtKeyIsName_insert_dataType_self
    {d : Source.Decls} (hP : SrcDtKeyIsName d) (dt : DataType) :
    SrcDtKeyIsName (d.insert dt.name (.dataType dt)) := by
  intro k dt' hget
  by_cases hkn : (dt.name == k) = true
  · have hkEq : dt.name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hget
    rw [← hget]
  · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' hget

private theorem SrcDtKeyIsName_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Source.Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcDtKeyIsName acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SrcDtKeyIsName acc'.2 := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  simp only
  exact SrcDtKeyIsName_insert_function hP _ _

private theorem SrcDtKeyIsName_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SrcDtKeyIsName init.2 →
      ctors.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SrcDtKeyIsName result.2 := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hP hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro init result hP hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hc
    split at hc
    · exact absurd hc (by intro h; cases h)
    · simp only [Except.ok.injEq] at hc
      subst hc
      apply ih _ result _ hfold
      exact SrcDtKeyIsName_insert_constructor hP _ _ _

private theorem SrcDtKeyIsName_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcDtKeyIsName acc.2)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SrcDtKeyIsName acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hdt'_name : ({ dataType with constructors } : DataType).name = dataType.name := rfl
  have hP_mid : SrcDtKeyIsName (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) := by
    rw [show dataType.name = ({ dataType with constructors } : DataType).name from hdt'_name.symm]
    exact SrcDtKeyIsName_insert_dataType_self hP { dataType with constructors }
  exact SrcDtKeyIsName_ctor_fold dataType.name { dataType with constructors }
    constructors _ acc' hP_mid hstep

private theorem SrcDtKeyIsName_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    SrcDtKeyIsName decls := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : SrcDtKeyIsName afterFns.2 := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · show SrcDtKeyIsName (aliasNames, (default : Source.Decls)).2
      exact SrcDtKeyIsName_default
    · intro a x a' _hmem hstep hP
      exact SrcDtKeyIsName_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' _hmem hstep hP
    exact SrcDtKeyIsName_dataTypeStep hP hstep

/-! ## Constructor-companion invariant for source decls.

`mkDecls_dataTypeStep` always inserts the `.dataType dt'` entry at
`dt'.name` (= `dataType.name`) BEFORE folding the constructors. The
subsequent constructor inserts use keys of the form
`dataType.name.pushNamespace c.nameHead`.

The key technical tool is the combined invariant `MkDeclsInv`, which pairs
the ctor-companion property with the `allNames` ⊇ `keys(decls)` bridge.
Since `mkDecls_dataTypeStep` checks `if allNames.contains ctorName` before
each constructor insert, we can rule out accidental overlap with prior dt
entries. -/

private theorem Name_str_ne_self_CS : ∀ (n : Lean.Name) (s : String),
    Lean.Name.str n s ≠ n
  | .anonymous, _, h => by cases h
  | .str n' s', s, h => by
    injection h with hn _hs
    exact Name_str_ne_self_CS n' s' hn
  | .num _ _, _, h => by cases h

private theorem ne_pushNamespace_self_CS (g : Global) (s : String) :
    g ≠ g.pushNamespace s := by
  intro h
  have h' : g.toName = g.toName.mkStr s := Global.mk.inj h
  have h'' : Lean.Name.str g.toName s = g.toName := h'.symm
  exact Name_str_ne_self_CS g.toName s h''

/-- `Global.pushNamespace` injectivity: equal pushed keys force equal prefixes. -/
private theorem pushNamespace_left_inj_CS {g₁ g₂ : Global} {s t : String}
    (h : g₁.pushNamespace s = g₂.pushNamespace t) : g₁ = g₂ := by
  have h' : g₁.toName.mkStr s = g₂.toName.mkStr t := Global.mk.inj h
  have h'' : Lean.Name.str g₁.toName s = Lean.Name.str g₂.toName t := h'
  have : g₁.toName = g₂.toName := by injection h''
  cases g₁; cases g₂; simp_all

/-- Joint invariant: `allNames` contains every key of `decls`, and
`SrcCtorCompanionP` holds. -/
private def MkDeclsInv (acc : Std.HashSet Global × Source.Decls) : Prop :=
  (∀ k d, acc.2.getByKey k = some d → acc.1.contains k = true) ∧
  (∀ k dt c, acc.2.getByKey k = some (.constructor dt c) →
    acc.2.getByKey dt.name = some (.dataType dt) ∧ c ∈ dt.constructors)

private theorem MkDeclsInv_default (allNames : Std.HashSet Global) :
    MkDeclsInv (allNames, (default : Source.Decls)) := by
  refine ⟨?_, ?_⟩ <;> intros k
  · intro d hget
    exfalso
    have hne : (default : Source.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Source.Decls).indices[k]?).bind _ = none
      have : (default : Source.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  · intro dt c hget
    exfalso
    have hne : (default : Source.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Source.Decls).indices[k]?).bind _ = none
      have : (default : Source.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget

private theorem MkDeclsInv_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {function : Source.Function}
    (hP : MkDeclsInv acc)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    MkDeclsInv acc' := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  have hnodup : acc.1.contains function.name = false := by
    cases hc : acc.1.contains function.name with
    | false => rfl
    | true =>
      exfalso
      rw [hc] at hstep
      simp only [↓reduceIte] at hstep
      cases hstep
  rw [hnodup] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  refine ⟨?_, ?_⟩
  · intro k d hget
    by_cases hkn : (function.name == k) = true
    · have hkEq : function.name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [Std.HashSet.contains_insert]
      simp
    · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      rw [Std.HashSet.contains_insert]
      simp [hP.1 k d hget]
  · intro k dt c hget
    by_cases hkn : (function.name == k) = true
    · have hkEq : function.name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      have ⟨hcomp, hmem⟩ := hP.2 k dt c hget
      -- We need init.2.getByKey dt.name = .dataType dt after function insert.
      -- dt.name might equal function.name? If so, the old .dataType dt would be
      -- overwritten by the new .function. But function.name was checked against
      -- allNames via hnodup: hnodup : allNames.contains function.name = false.
      -- And hP.1 gives: .getByKey k = some d → allNames.contains k. So dt.name
      -- is in allNames. So dt.name ≠ function.name.
      have hdt_ne : (function.name == dt.name) = false := by
        cases hbeq : (function.name == dt.name) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hbeq
          rw [heq] at hnodup
          have hcontains := hP.1 dt.name (.dataType dt) hcomp
          rw [hnodup] at hcontains
          cases hcontains
      refine ⟨?_, hmem⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hdt_ne]
      exact hcomp

/-- Inner ctor fold preserves `MkDeclsInv`, given that the dt companion is
present before the fold and that dt.name is in allNames (already from the
outer step). -/
private theorem MkDeclsInv_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors_to_fold : List Constructor)
      (ctors_already : List Constructor)
      (init result : Std.HashSet Global × Source.Decls),
      MkDeclsInv init →
      init.2.getByKey dataTypeName = some (.dataType dataType') →
      dataType'.name = dataTypeName →
      dataType'.constructors = ctors_already ++ ctors_to_fold →
      ctors_to_fold.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      MkDeclsInv result := by
  intro ctors_to_fold
  induction ctors_to_fold with
  | nil =>
    intro _ init result hP _hdt _hname _hctors hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro ctors_already init result hP hdt hdtname hctors hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    have hnodup_ctor : init.1.contains (dataTypeName.pushNamespace c.nameHead) = false := by
      cases hc : init.1.contains (dataTypeName.pushNamespace c.nameHead) with
      | false => rfl
      | true =>
        exfalso
        rw [hc] at hfold
        simp only [↓reduceIte] at hfold
        cases hfold
    rw [hnodup_ctor] at hfold
    simp only [Bool.false_eq_true, ↓reduceIte] at hfold
    have hc_in_dt : c ∈ dataType'.constructors := by
      rw [hctors]; exact List.mem_append.mpr (.inr List.mem_cons_self)
    -- Establish MkDeclsInv for acc' = after inserting at pushed ctorName.
    have hPnew : MkDeclsInv (init.1.insert (dataTypeName.pushNamespace c.nameHead),
                             init.2.insert (dataTypeName.pushNamespace c.nameHead)
                               (.constructor dataType' c)) := by
      refine ⟨?_, ?_⟩
      · intro k d hget
        by_cases hkn : (dataTypeName.pushNamespace c.nameHead == k) = true
        · have hkEq := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [Std.HashSet.contains_insert]; simp
        · have hne : (dataTypeName.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          rw [Std.HashSet.contains_insert]; simp [hP.1 k d hget]
      · intro k dt cc hget
        by_cases hkn : (dataTypeName.pushNamespace c.nameHead == k) = true
        · have hkEq := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hget
          obtain ⟨heq1, heq2⟩ := hget
          rw [← heq1, ← heq2]
          -- dt.name = dataType'.name = dataTypeName.
          rw [hdtname]
          refine ⟨?_, hc_in_dt⟩
          have hne : (dataTypeName.pushNamespace c.nameHead == dataTypeName) = false := by
            cases hbeq : (dataTypeName.pushNamespace c.nameHead == dataTypeName) with
            | false => rfl
            | true =>
              exfalso
              have heq := LawfulBEq.eq_of_beq hbeq
              exact (ne_pushNamespace_self_CS dataTypeName c.nameHead) heq.symm
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hdt
        · have hne : (dataTypeName.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          have ⟨hcomp, hmemcc⟩ := hP.2 k dt cc hget
          refine ⟨?_, hmemcc⟩
          -- Need to show insert(init.2, pushedCtorName, ...).getByKey dt.name = dataType dt.
          -- If pushedCtorName ≠ dt.name, trivial. If =, contradiction via allNames.
          have hdt_ne : (dataTypeName.pushNamespace c.nameHead == dt.name) = false := by
            cases hbeq : (dataTypeName.pushNamespace c.nameHead == dt.name) with
            | false => rfl
            | true =>
              exfalso
              have heq := LawfulBEq.eq_of_beq hbeq
              -- dt.name is a key of init.2, so allNames.contains dt.name = true.
              have hdt_contains := hP.1 dt.name (.dataType dt) hcomp
              -- But allNames.contains (pushedCtorName) = false (hnodup_ctor).
              rw [heq] at hnodup_ctor
              rw [hnodup_ctor] at hdt_contains
              cases hdt_contains
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hdt_ne]
          exact hcomp
    have hdt_new : (init.2.insert (dataTypeName.pushNamespace c.nameHead)
        (.constructor dataType' c)).getByKey dataTypeName =
        some (.dataType dataType') := by
      have hne : (dataTypeName.pushNamespace c.nameHead == dataTypeName) = false := by
        cases hbeq : (dataTypeName.pushNamespace c.nameHead == dataTypeName) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hbeq
          exact (ne_pushNamespace_self_CS dataTypeName c.nameHead) heq.symm
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hdt
    exact ih (ctors_already ++ [c]) _ result hPnew hdt_new hdtname
      (by rw [List.append_assoc, List.singleton_append]; exact hctors) hfold

/-- After the dt-insert (mid-state of `dataTypeStep`), `MkDeclsInv` holds.
Extracted helper from `MkDeclsInv_dataTypeStep`'s body. -/
private theorem MkDeclsInv_dataTypeStep_mid
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {constructors : List Constructor}
    (hP : MkDeclsInv acc)
    (hnodup_dt : acc.1.contains dataType.name = false) :
    MkDeclsInv (acc.1.insert dataType.name,
                acc.2.insert dataType.name
                  (.dataType { dataType with constructors })) := by
  let dt' : DataType := { dataType with constructors }
  refine ⟨?_, ?_⟩
  · intro k d hget
    by_cases hkn : (dataType.name == k) = true
    · have hkEq := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [Std.HashSet.contains_insert]; simp
    · have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      rw [Std.HashSet.contains_insert]; simp [hP.1 k d hget]
  · intro k dt'' cc hget
    by_cases hkn : (dataType.name == k) = true
    · have hkEq := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      have ⟨hcomp, hmemcc⟩ := hP.2 k dt'' cc hget
      refine ⟨?_, hmemcc⟩
      have hdt_ne : (dataType.name == dt''.name) = false := by
        cases hbeq : (dataType.name == dt''.name) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hbeq
          have hdt_contains := hP.1 dt''.name (.dataType dt'') hcomp
          rw [← heq] at hdt_contains
          rw [hnodup_dt] at hdt_contains
          cases hdt_contains
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hdt_ne]
      exact hcomp

/-- Inner ctor fold inserts at each ctor's pushNamespaced key. After completion,
every ctor in `dataType'.constructors = ctors_already ++ ctors_to_fold` has its
key entry. Parameterized by `ctors_already` for inductive walk. -/
private theorem ctor_fold_inserts_all
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors_to_fold : List Constructor)
      (ctors_already : List Constructor)
      (init result : Std.HashSet Global × Source.Decls),
      MkDeclsInv init →
      init.2.getByKey dataTypeName = some (.dataType dataType') →
      dataType'.name = dataTypeName →
      dataType'.constructors = ctors_already ++ ctors_to_fold →
      (∀ c ∈ ctors_already,
        init.2.getByKey (dataTypeName.pushNamespace c.nameHead) =
          some (.constructor dataType' c)) →
      ctors_to_fold.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      ∀ c ∈ dataType'.constructors,
        result.2.getByKey (dataTypeName.pushNamespace c.nameHead) =
          some (.constructor dataType' c) := by
  intro ctors_to_fold
  induction ctors_to_fold with
  | nil =>
    intro ctors_already init result _hP _hdt _hname hctors hQctors hfold c hc
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold
    rw [hctors, List.append_nil] at hc
    exact hQctors c hc
  | cons c rest ih =>
    intro ctors_already init result hP hdt hdtname hctors hQctors hfold c' hc'
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    have hnodup_ctor : init.1.contains (dataTypeName.pushNamespace c.nameHead) = false := by
      cases hc : init.1.contains (dataTypeName.pushNamespace c.nameHead) with
      | false => rfl
      | true =>
        exfalso
        rw [hc] at hfold
        simp only [↓reduceIte] at hfold
        cases hfold
    rw [hnodup_ctor] at hfold
    simp only [Bool.false_eq_true, ↓reduceIte] at hfold
    let next_decls := init.2.insert (dataTypeName.pushNamespace c.nameHead)
                        (.constructor dataType' c)
    let next_allNames := init.1.insert (dataTypeName.pushNamespace c.nameHead)
    have hPnext : MkDeclsInv (next_allNames, next_decls) := by
      refine ⟨?_, ?_⟩
      · intro k d hget
        by_cases hkn : (dataTypeName.pushNamespace c.nameHead == k) = true
        · have hkEq := LawfulBEq.eq_of_beq hkn
          subst hkEq
          show next_allNames.contains _ = true
          rw [Std.HashSet.contains_insert]; simp
        · have hne : (dataTypeName.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          show next_allNames.contains k = true
          rw [Std.HashSet.contains_insert]
          show ((dataTypeName.pushNamespace c.nameHead == k) || init.1.contains k) = true
          rw [hne]; simp
          change next_decls.getByKey k = some d at hget
          rw [show next_decls.getByKey k = init.2.getByKey k from
            IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP.1 k d hget
      · intro k dt cc hget
        by_cases hkn : (dataTypeName.pushNamespace c.nameHead == k) = true
        · have hkEq := LawfulBEq.eq_of_beq hkn
          subst hkEq
          change next_decls.getByKey (dataTypeName.pushNamespace c.nameHead) =
            some (.constructor dt cc) at hget
          rw [show next_decls.getByKey (dataTypeName.pushNamespace c.nameHead) =
            some (.constructor dataType' c) from IndexMap.getByKey_insert_self _ _ _] at hget
          simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hget
          obtain ⟨heq1, heq2⟩ := hget
          rw [← heq1, ← heq2]
          rw [hdtname]
          have hc_in_dt : c ∈ dataType'.constructors := by
            rw [hctors]; exact List.mem_append.mpr (.inr List.mem_cons_self)
          refine ⟨?_, hc_in_dt⟩
          have hne : (dataTypeName.pushNamespace c.nameHead == dataTypeName) = false := by
            cases hbeq : (dataTypeName.pushNamespace c.nameHead == dataTypeName) with
            | false => rfl
            | true =>
              exfalso
              have heq := LawfulBEq.eq_of_beq hbeq
              exact (ne_pushNamespace_self_CS dataTypeName c.nameHead) heq.symm
          show next_decls.getByKey dataTypeName = some (.dataType dataType')
          rw [show next_decls.getByKey dataTypeName = init.2.getByKey dataTypeName from
            IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hdt
        · have hne : (dataTypeName.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          change next_decls.getByKey k = some (.constructor dt cc) at hget
          rw [show next_decls.getByKey k = init.2.getByKey k from
            IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          have ⟨hcomp, hmemcc⟩ := hP.2 k dt cc hget
          refine ⟨?_, hmemcc⟩
          have hdt_ne : (dataTypeName.pushNamespace c.nameHead == dt.name) = false := by
            cases hbeq : (dataTypeName.pushNamespace c.nameHead == dt.name) with
            | false => rfl
            | true =>
              exfalso
              have heq := LawfulBEq.eq_of_beq hbeq
              have hdt_contains := hP.1 dt.name (.dataType dt) hcomp
              rw [heq] at hnodup_ctor
              rw [hnodup_ctor] at hdt_contains
              cases hdt_contains
          show next_decls.getByKey dt.name = some (.dataType dt)
          rw [show next_decls.getByKey dt.name = init.2.getByKey dt.name from
            IndexMap.getByKey_insert_of_beq_false _ _ hdt_ne]
          exact hcomp
    have hQctorsNext : ∀ c'' ∈ ctors_already ++ [c],
        next_decls.getByKey (dataTypeName.pushNamespace c''.nameHead) =
          some (.constructor dataType' c'') := by
      intro c'' hc''
      rcases List.mem_append.mp hc'' with hc'' | hc''
      · have hold := hQctors c'' hc''
        by_cases hkeq : (dataTypeName.pushNamespace c.nameHead ==
                          dataTypeName.pushNamespace c''.nameHead) = true
        · exfalso
          have heq := LawfulBEq.eq_of_beq hkeq
          have hin := hP.1 _ _ hold
          rw [← heq] at hin
          rw [hnodup_ctor] at hin
          cases hin
        · have hne : (dataTypeName.pushNamespace c.nameHead ==
                       dataTypeName.pushNamespace c''.nameHead) = false :=
            Bool.not_eq_true _ |>.mp hkeq
          show next_decls.getByKey (dataTypeName.pushNamespace c''.nameHead) =
            some (.constructor dataType' c'')
          rw [show next_decls.getByKey (dataTypeName.pushNamespace c''.nameHead) =
            init.2.getByKey (dataTypeName.pushNamespace c''.nameHead) from
            IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hold
      · simp only [List.mem_singleton] at hc''
        subst hc''
        show next_decls.getByKey (dataTypeName.pushNamespace c''.nameHead) =
          some (.constructor dataType' c'')
        exact IndexMap.getByKey_insert_self _ _ _
    have hdt_next : next_decls.getByKey dataTypeName = some (.dataType dataType') := by
      have hne : (dataTypeName.pushNamespace c.nameHead == dataTypeName) = false := by
        cases hbeq : (dataTypeName.pushNamespace c.nameHead == dataTypeName) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hbeq
          exact (ne_pushNamespace_self_CS dataTypeName c.nameHead) heq.symm
      show next_decls.getByKey dataTypeName = some (.dataType dataType')
      rw [show next_decls.getByKey dataTypeName = init.2.getByKey dataTypeName from
        IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hdt
    have hctors_next : dataType'.constructors = (ctors_already ++ [c]) ++ rest := by
      rw [hctors, List.append_assoc]; rfl
    exact ih (ctors_already ++ [c]) (next_allNames, next_decls) result hPnext hdt_next
      hdtname hctors_next hQctorsNext hfold c' hc'

/-- Inner ctor fold preserves `getByKey` at keys not equal to any inserted ctor key.
The hypothesis `hk` requires `(dataTypeName.pushNamespace c.nameHead == k) = false`
for every `c` that will be folded over. -/
private theorem ctor_fold_preserves_other_key
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors_to_fold : List Constructor)
      (init result : Std.HashSet Global × Source.Decls),
      ctors_to_fold.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      ∀ k, (∀ c ∈ ctors_to_fold, (dataTypeName.pushNamespace c.nameHead == k) = false) →
        result.2.getByKey k = init.2.getByKey k := by
  intro ctors_to_fold
  induction ctors_to_fold with
  | nil =>
    intro init result hfold k _hk
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; rfl
  | cons c rest ih =>
    intro init result hfold k hk
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    have hnodup_ctor : init.1.contains (dataTypeName.pushNamespace c.nameHead) = false := by
      cases hc : init.1.contains (dataTypeName.pushNamespace c.nameHead) with
      | false => rfl
      | true => exfalso; rw [hc] at hfold; simp only [↓reduceIte] at hfold; cases hfold
    rw [hnodup_ctor] at hfold
    simp only [Bool.false_eq_true, ↓reduceIte] at hfold
    let next_decls := init.2.insert (dataTypeName.pushNamespace c.nameHead)
                        (.constructor dataType' c)
    let next_allNames := init.1.insert (dataTypeName.pushNamespace c.nameHead)
    have hk_ne : (dataTypeName.pushNamespace c.nameHead == k) = false :=
      hk c List.mem_cons_self
    have hk_rest : ∀ c' ∈ rest, (dataTypeName.pushNamespace c'.nameHead == k) = false := by
      intro c' hc'
      exact hk c' (List.mem_cons_of_mem _ hc')
    have hres := ih (next_allNames, next_decls) result hfold k hk_rest
    rw [hres]
    show next_decls.getByKey k = init.2.getByKey k
    rw [show next_decls.getByKey k = init.2.getByKey k from
      IndexMap.getByKey_insert_of_beq_false _ _ hk_ne]

private theorem MkDeclsInv_ctor_fold_dt_preserved
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors_to_fold : List Constructor)
      (init result : Std.HashSet Global × Source.Decls),
      init.2.getByKey dataTypeName = some (.dataType dataType') →
      ctors_to_fold.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      result.2.getByKey dataTypeName = some (.dataType dataType') := by
  intro ctors_to_fold init result hdt hfold
  have hk : ∀ c ∈ ctors_to_fold,
      (dataTypeName.pushNamespace c.nameHead == dataTypeName) = false := by
    intro c _hc
    cases hbeq : (dataTypeName.pushNamespace c.nameHead == dataTypeName) with
    | false => rfl
    | true =>
      exfalso
      have heq := LawfulBEq.eq_of_beq hbeq
      exact (ne_pushNamespace_self_CS dataTypeName c.nameHead) heq.symm
  have hpres := ctor_fold_preserves_other_key dataTypeName dataType' ctors_to_fold
    init result hfold dataTypeName hk
  rw [hpres]; exact hdt

private theorem MkDeclsInv_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {dataType : DataType}
    (hP : MkDeclsInv acc)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    MkDeclsInv acc' := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  have hnodup_dt : acc.1.contains dataType.name = false := by
    cases hc : acc.1.contains dataType.name with
    | false => rfl
    | true =>
      exfalso
      rw [hc] at hstep
      simp only [↓reduceIte] at hstep
      cases hstep
  rw [hnodup_dt] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  -- Intermediate state after inserting the dt at dataType.name.
  have hdt'_name : ({ dataType with constructors } : DataType).name = dataType.name := rfl
  let dt' : DataType := { dataType with constructors }
  have hdt'_def : dt' = { dataType with constructors } := rfl
  -- Show MkDeclsInv for the (allNames.insert dataType.name, decls.insert dataType.name ...) state.
  have hPmid : MkDeclsInv (acc.1.insert dataType.name,
                           acc.2.insert dataType.name (.dataType dt')) := by
    refine ⟨?_, ?_⟩
    · intro k d hget
      by_cases hkn : (dataType.name == k) = true
      · have hkEq := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [Std.HashSet.contains_insert]; simp
      · have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        rw [Std.HashSet.contains_insert]; simp [hP.1 k d hget]
    · intro k dt'' cc hget
      by_cases hkn : (dataType.name == k) = true
      · have hkEq := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        have ⟨hcomp, hmemcc⟩ := hP.2 k dt'' cc hget
        refine ⟨?_, hmemcc⟩
        have hdt_ne : (dataType.name == dt''.name) = false := by
          cases hbeq : (dataType.name == dt''.name) with
          | false => rfl
          | true =>
            exfalso
            have heq := LawfulBEq.eq_of_beq hbeq
            -- dt''.name is a key of acc.2, so allNames.contains dt''.name = true.
            have hdt_contains := hP.1 dt''.name (.dataType dt'') hcomp
            rw [← heq] at hdt_contains
            rw [hnodup_dt] at hdt_contains
            cases hdt_contains
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hdt_ne]
        exact hcomp
  have hdt_mid : (acc.2.insert dataType.name (.dataType dt')).getByKey dataType.name =
      some (.dataType dt') := IndexMap.getByKey_insert_self _ _ _
  exact MkDeclsInv_ctor_fold dataType.name dt' constructors [] _ _ hPmid hdt_mid rfl rfl hstep

private theorem MkDeclsInv_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    ∃ allNames, MkDeclsInv (allNames, decls) := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : MkDeclsInv afterFns := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · exact MkDeclsInv_default aliasNames
    · intro a x a' _hmem hstep hP
      exact MkDeclsInv_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  refine ⟨afterDts.1, ?_⟩
  have : afterDts = (afterDts.1, afterDts.2) := rfl
  rw [this]
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' _hmem hstep hP
    exact MkDeclsInv_dataTypeStep hP hstep

/-- Public: `mkDecls` establishes the ctor-companion invariant. -/
theorem mkDecls_ctor_companion
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt c, decls.getByKey k = some (.constructor dt c) →
      decls.getByKey dt.name = some (.dataType dt) ∧ c ∈ dt.constructors := by
  obtain ⟨_, hInv⟩ := MkDeclsInv_mkDecls hdecls
  exact hInv.2

/-- Public: `mkDecls` establishes dt-key-is-name for sources. -/
theorem mkDecls_dt_key_is_name
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt, decls.getByKey k = some (.dataType dt) → k = dt.name :=
  SrcDtKeyIsName_mkDecls hdecls

/-! ## `mkDecls_dt_implies_ctor_keys` — dual of `mkDecls_ctor_companion`.

For each `(k, dt)` where `decls.getByKey k = some (.dataType dt)`, every
`c ∈ dt.constructors` has `decls.getByKey (k.pushNamespace c.nameHead) =
some (.constructor dt c)`. Built via tracking the accumulator-parameterized
invariant `Q` through the `mkDecls` outer fold. -/

/-- Combined invariant: original `MkDeclsInv` AND the dt→ctor existence guarantee. -/
private def MkDeclsInvDtCtor (acc : Std.HashSet Global × Source.Decls) : Prop :=
  MkDeclsInv acc ∧
  ∀ k dt, acc.2.getByKey k = some (.dataType dt) →
    ∀ c ∈ dt.constructors,
      acc.2.getByKey (k.pushNamespace c.nameHead) = some (.constructor dt c)

private theorem MkDeclsInvDtCtor_default (allNames : Std.HashSet Global) :
    MkDeclsInvDtCtor (allNames, (default : Source.Decls)) := by
  refine ⟨MkDeclsInv_default allNames, ?_⟩
  intro k dt hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

/-- `functionStep` preserves the combined invariant. Insert at `function.name`
doesn't touch any dt-keys or ctor-keys (else duplicatedDefinition). -/
private theorem MkDeclsInvDtCtor_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {function : Source.Function}
    (hP : MkDeclsInvDtCtor acc)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    MkDeclsInvDtCtor acc' := by
  refine ⟨MkDeclsInv_functionStep hP.1 hstep, ?_⟩
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  have hnodup : acc.1.contains function.name = false := by
    cases hc : acc.1.contains function.name with
    | false => rfl
    | true => exfalso; rw [hc] at hstep; simp only [↓reduceIte] at hstep; cases hstep
  rw [hnodup] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i instantiated _hinst
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i output _houtput
  simp only [Except.ok.injEq] at hstep
  intro k dt hget c hc
  by_cases hkn : (function.name == k) = true
  · exfalso
    have hkEq := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [← hstep] at hget
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [← hstep] at hget
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    have hold := hP.2 k dt hget c hc
    by_cases hkn2 : (function.name == k.pushNamespace c.nameHead) = true
    · exfalso
      have heq := LawfulBEq.eq_of_beq hkn2
      have hin := hP.1.1 _ _ hold
      rw [← heq] at hin
      rw [hnodup] at hin
      cases hin
    · have hne2 : (function.name == k.pushNamespace c.nameHead) = false :=
        Bool.not_eq_true _ |>.mp hkn2
      rw [← hstep]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne2]
      exact hold

/-- `dataTypeStep` preserves the combined invariant. After the outer dt-insert
+ inner ctor fold, every dt entry's ctors are present. -/
private theorem MkDeclsInvDtCtor_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {dataType : DataType}
    (hP : MkDeclsInvDtCtor acc)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    MkDeclsInvDtCtor acc' := by
  have hPnew : MkDeclsInv acc' := MkDeclsInv_dataTypeStep hP.1 hstep
  refine ⟨hPnew, ?_⟩
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  have hnodup_dt : acc.1.contains dataType.name = false := by
    cases hc : acc.1.contains dataType.name with
    | false => rfl
    | true => exfalso; rw [hc] at hstep; simp only [↓reduceIte] at hstep; cases hstep
  rw [hnodup_dt] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  let dt' : DataType := { dataType with constructors }
  -- After step: acc' = ctor_fold(insert dt at dt.name, constructors).
  -- The inner ctor fold inserts at each c.nameHead.
  -- Use `ctor_fold_inserts_all_with_others` helper.
  intro k dt'' hget c hc
  -- Three sub-cases: k = dataType.name, k = ctor key (impossible — k has dt), or k other.
  -- Apply MkDeclsInv on acc' (already established) to get k = dt''.name.
  -- Then either dt'' = dt' (new dt) or dt'' was already in acc.
  by_cases hkn : (dataType.name == k) = true
  · -- New dt: dt'' = dt'.
    have hkEq := LawfulBEq.eq_of_beq hkn
    subst hkEq
    -- Need: acc'.2 has ctor at dataType.name.pushNamespace c.nameHead = some (.ctor dt' c).
    -- This follows from ctor_fold_inserts_all + dt'' = dt'.
    -- First derive dt'' = dt' from hget.
    have hdt''_eq : dt'' = dt' := by
      have hdt_init : (acc.1.insert dataType.name,
                      acc.2.insert dataType.name (.dataType dt')).2.getByKey dataType.name =
          some (.dataType dt') := IndexMap.getByKey_insert_self _ _ _
      have h := MkDeclsInv_ctor_fold_dt_preserved dataType.name dt' constructors
        _ acc' hdt_init hstep
      rw [h] at hget
      cases hget; rfl
    subst hdt''_eq
    -- Now: need ctor at dataType.name.pushNamespace c.nameHead with c ∈ dt'.constructors.
    apply ctor_fold_inserts_all dataType.name dt' constructors []
      (acc.1.insert dataType.name, acc.2.insert dataType.name (.dataType dt')) acc'
      (MkDeclsInv_dataTypeStep_mid hP.1 hnodup_dt)
      (IndexMap.getByKey_insert_self _ _ _) rfl rfl
      (fun c hc => absurd hc List.not_mem_nil) hstep c hc
  · -- Old dt: k ≠ dataType.name. dt'' was in acc.2 already.
    have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    -- acc' = ctor_fold(insert dt at dt.name, constructors).
    -- Insert at dt.name doesn't touch k (hne). Inner ctor fold inserts at ctor keys.
    -- Old dt at k preserved through both. Old dt's ctors at k.pushNamespace c.nameHead
    -- preserved (those keys are in acc.1, ctor fold inserts at NEW keys not in acc.1).
    have hget_acc : acc.2.getByKey k = some (.dataType dt'') := by
      -- k is not any newly inserted ctor key — else acc' would have a constructor at k.
      have hk_no_ctor : ∀ c' ∈ constructors,
          (dataType.name.pushNamespace c'.nameHead == k) = false := by
        intro c' hc'
        cases hbeq : (dataType.name.pushNamespace c'.nameHead == k) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hbeq
          -- ctor_fold_inserts_all says acc'.2 has constructor at this key.
          have hctor := ctor_fold_inserts_all dataType.name dt' constructors []
            (acc.1.insert dataType.name, acc.2.insert dataType.name (.dataType dt')) acc'
            (MkDeclsInv_dataTypeStep_mid hP.1 hnodup_dt)
            (IndexMap.getByKey_insert_self _ _ _) rfl rfl
            (fun _ hc => absurd hc List.not_mem_nil) hstep c' hc'
          rw [heq] at hctor
          rw [hctor] at hget
          cases hget
      have hpres := ctor_fold_preserves_other_key dataType.name dt' constructors
        _ acc' hstep k hk_no_ctor
      rw [hpres] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hget
    have hold := hP.2 k dt'' hget_acc c hc
    -- Show acc'.2 has same ctor entry. Use ctor_fold preservation.
    have hctor_in : acc.1.contains (k.pushNamespace c.nameHead) = true :=
      hP.1.1 _ _ hold
    -- After insert at dt.name (≠ k.pushNamespace c.nameHead, by hctor_in vs hnodup_dt mismatch):
    have hne_dt_ctor : (dataType.name == k.pushNamespace c.nameHead) = false := by
      cases hbeq : (dataType.name == k.pushNamespace c.nameHead) with
      | false => rfl
      | true =>
        exfalso
        have heq := LawfulBEq.eq_of_beq hbeq
        rw [← heq] at hctor_in
        rw [hnodup_dt] at hctor_in
        cases hctor_in
    -- After ctor fold: insert at dataType.name.pushNamespace c'.nameHead for each c' ∈ constructors.
    -- These are in acc'.1 but not in acc.1.
    -- For old key k.pushNamespace c.nameHead (in acc.1), preserved.
    have hk_no_ctor : ∀ c' ∈ constructors,
        (dataType.name.pushNamespace c'.nameHead == k.pushNamespace c.nameHead) = false := by
      intro c' _hc'
      cases hbeq : (dataType.name.pushNamespace c'.nameHead ==
                     k.pushNamespace c.nameHead) with
      | false => rfl
      | true =>
        exfalso
        have heq := LawfulBEq.eq_of_beq hbeq
        have hname_eq : dataType.name = k := pushNamespace_left_inj_CS heq
        rw [hname_eq] at hne
        simp at hne
    have hpres := ctor_fold_preserves_other_key dataType.name dt' constructors
      _ acc' hstep (k.pushNamespace c.nameHead) hk_no_ctor
    rw [hpres]
    -- Show: insert at dataType.name (= mid_state) preserves at this key (≠ dataType.name).
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_dt_ctor]
    exact hold

private theorem MkDeclsInvDtCtor_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    ∃ allNames, MkDeclsInvDtCtor (allNames, decls) := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : MkDeclsInvDtCtor afterFns := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · exact MkDeclsInvDtCtor_default aliasNames
    · intro a x a' _hmem hstep hP
      exact MkDeclsInvDtCtor_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  refine ⟨afterDts.1, ?_⟩
  have heq : afterDts = (afterDts.1, afterDts.2) := rfl
  rw [heq]
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' _hmem hstep hP
    exact MkDeclsInvDtCtor_dataTypeStep hP hstep

/-- Public dual: `mkDecls` establishes that every dt's constructors all have
their ctor key entries. Mirror of `mkDecls_ctor_companion`. -/
theorem mkDecls_dt_implies_ctor_keys
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt, decls.getByKey k = some (.dataType dt) →
      ∀ c ∈ dt.constructors,
        decls.getByKey (k.pushNamespace c.nameHead) = some (.constructor dt c) := by
  obtain ⟨_, hInv⟩ := MkDeclsInvDtCtor_mkDecls hdecls
  exact hInv.2

/-! ## Constructor `nameHead` positional distinctness.

For each `(k, .dataType dt) ∈ decls`, the entries of `dt.constructors`
have positionally-distinct `nameHead`s. Reason: the inner ctor fold of
`mkDecls_dataTypeStep` checks `allNames.contains (k.pushNamespace c.nameHead)`
before each insert, so equal `nameHead`s would force a duplicate-key error. -/

/-- Inner ctor-fold success forces positional `nameHead` distinctness on
`ctors_already ++ ctors_to_fold`, given that `ctors_already` is already
distinct and all of its pushed keys are present in `init.1`. -/
private theorem ctor_fold_nameHeads_distinct
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors_to_fold : List Constructor)
      (ctors_already : List Constructor)
      (init result : Std.HashSet Global × Source.Decls),
      (∀ c ∈ ctors_already,
        init.1.contains (dataTypeName.pushNamespace c.nameHead) = true) →
      (∀ i j (hi : i < ctors_already.length) (hj : j < ctors_already.length),
        (ctors_already[i]'hi).nameHead = (ctors_already[j]'hj).nameHead → i = j) →
      ctors_to_fold.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      ∀ i j (hi : i < (ctors_already ++ ctors_to_fold).length)
              (hj : j < (ctors_already ++ ctors_to_fold).length),
        ((ctors_already ++ ctors_to_fold)[i]'hi).nameHead =
          ((ctors_already ++ ctors_to_fold)[j]'hj).nameHead → i = j := by
  intro ctors_to_fold
  induction ctors_to_fold with
  | nil =>
    intro ctors_already _init _result _hcontains hdistinct _hfold i j hi hj heq
    have hi' : i < ctors_already.length := by
      have := hi; rw [List.append_nil] at this; exact this
    have hj' : j < ctors_already.length := by
      have := hj; rw [List.append_nil] at this; exact this
    have hgi : (ctors_already ++ [])[i]'hi = ctors_already[i]'hi' := by
      simp
    have hgj : (ctors_already ++ [])[j]'hj = ctors_already[j]'hj' := by
      simp
    rw [hgi, hgj] at heq
    exact hdistinct i j hi' hj' heq
  | cons c rest ih =>
    intro ctors_already init result hcontains hdistinct hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    have hnodup_ctor : init.1.contains (dataTypeName.pushNamespace c.nameHead) = false := by
      cases hc : init.1.contains (dataTypeName.pushNamespace c.nameHead) with
      | false => rfl
      | true => exfalso; rw [hc] at hfold; simp only [↓reduceIte] at hfold; cases hfold
    rw [hnodup_ctor] at hfold
    simp only [Bool.false_eq_true, ↓reduceIte] at hfold
    let next_decls := init.2.insert (dataTypeName.pushNamespace c.nameHead)
                        (.constructor dataType' c)
    let next_allNames := init.1.insert (dataTypeName.pushNamespace c.nameHead)
    have hcontains_next : ∀ c' ∈ ctors_already ++ [c],
        next_allNames.contains (dataTypeName.pushNamespace c'.nameHead) = true := by
      intro c' hc'
      show (init.1.insert _).contains _ = true
      rw [Std.HashSet.contains_insert]
      rcases List.mem_append.mp hc' with hc' | hc'
      · simp [hcontains c' hc']
      · simp only [List.mem_singleton] at hc'; subst hc'; simp
    have hdistinct_next :
        ∀ i j (hi : i < (ctors_already ++ [c]).length) (hj : j < (ctors_already ++ [c]).length),
          ((ctors_already ++ [c])[i]'hi).nameHead =
            ((ctors_already ++ [c])[j]'hj).nameHead → i = j := by
      intro i j hi hj heq
      have hi_bound : i < ctors_already.length + 1 := by
        have := hi; rw [List.length_append, List.length_singleton] at this; exact this
      have hj_bound : j < ctors_already.length + 1 := by
        have := hj; rw [List.length_append, List.length_singleton] at this; exact this
      by_cases hi_lt : i < ctors_already.length
      · by_cases hj_lt : j < ctors_already.length
        · -- both in ctors_already
          have hi_eq : (ctors_already ++ [c])[i]'hi = ctors_already[i]'hi_lt :=
            List.getElem_append_left hi_lt
          have hj_eq : (ctors_already ++ [c])[j]'hj = ctors_already[j]'hj_lt :=
            List.getElem_append_left hj_lt
          rw [hi_eq, hj_eq] at heq
          exact hdistinct i j hi_lt hj_lt heq
        · -- j = ctors_already.length, i in already → contradiction via push_inj
          exfalso
          have hj_eq_len : j = ctors_already.length := by omega
          subst hj_eq_len
          have hi_e : (ctors_already ++ [c])[i]'hi = ctors_already[i]'hi_lt :=
            List.getElem_append_left hi_lt
          have hj_e : (ctors_already ++ [c])[ctors_already.length]'hj = c := by
            rw [List.getElem_append_right (Nat.le_refl _)]; simp
          rw [hi_e, hj_e] at heq
          have hpush_eq : dataTypeName.pushNamespace (ctors_already[i]'hi_lt).nameHead =
              dataTypeName.pushNamespace c.nameHead := by rw [heq]
          have hcontains_i := hcontains _ (List.getElem_mem hi_lt)
          rw [hpush_eq] at hcontains_i
          rw [hnodup_ctor] at hcontains_i
          cases hcontains_i
      · by_cases hj_lt : j < ctors_already.length
        · -- i = ctors_already.length, j in already → symmetric contradiction
          exfalso
          have hi_eq_len : i = ctors_already.length := by omega
          subst hi_eq_len
          have hi_e : (ctors_already ++ [c])[ctors_already.length]'hi = c := by
            rw [List.getElem_append_right (Nat.le_refl _)]; simp
          have hj_e : (ctors_already ++ [c])[j]'hj = ctors_already[j]'hj_lt :=
            List.getElem_append_left hj_lt
          rw [hi_e, hj_e] at heq
          have hpush_eq : dataTypeName.pushNamespace c.nameHead =
              dataTypeName.pushNamespace (ctors_already[j]'hj_lt).nameHead := by rw [heq]
          have hcontains_j := hcontains _ (List.getElem_mem hj_lt)
          rw [← hpush_eq] at hcontains_j
          rw [hnodup_ctor] at hcontains_j
          cases hcontains_j
        · -- both = ctors_already.length
          omega
    have hres := ih (ctors_already ++ [c]) (next_allNames, next_decls) result
      hcontains_next hdistinct_next hfold
    -- Compose: (ctors_already ++ [c]) ++ rest = ctors_already ++ (c :: rest).
    intro i j hi hj heq
    have hassoc : (ctors_already ++ [c]) ++ rest = ctors_already ++ (c :: rest) := by
      rw [List.append_assoc]; rfl
    have hi' : i < ((ctors_already ++ [c]) ++ rest).length := by rw [hassoc]; exact hi
    have hj' : j < ((ctors_already ++ [c]) ++ rest).length := by rw [hassoc]; exact hj
    have heq' : (((ctors_already ++ [c]) ++ rest)[i]'hi').nameHead =
        (((ctors_already ++ [c]) ++ rest)[j]'hj').nameHead := by
      have hgi : ((ctors_already ++ [c]) ++ rest)[i]'hi' =
          (ctors_already ++ (c :: rest))[i]'hi := by congr 1 <;> rw [hassoc]
      have hgj : ((ctors_already ++ [c]) ++ rest)[j]'hj' =
          (ctors_already ++ (c :: rest))[j]'hj := by congr 1 <;> rw [hassoc]
      rw [hgi, hgj]; exact heq
    exact hres i j hi' hj' heq'

/-- Combined invariant: `MkDeclsInv` AND positional `nameHead` distinctness on
every dt's constructor list. -/
private def MkDeclsInvDistinct (acc : Std.HashSet Global × Source.Decls) : Prop :=
  MkDeclsInv acc ∧
  ∀ k dt, acc.2.getByKey k = some (.dataType dt) →
    ∀ i j (hi : i < dt.constructors.length) (hj : j < dt.constructors.length),
      (dt.constructors[i]'hi).nameHead = (dt.constructors[j]'hj).nameHead → i = j

private theorem MkDeclsInvDistinct_default (allNames : Std.HashSet Global) :
    MkDeclsInvDistinct (allNames, (default : Source.Decls)) := by
  refine ⟨MkDeclsInv_default allNames, ?_⟩
  intro k dt hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem MkDeclsInvDistinct_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {function : Source.Function}
    (hP : MkDeclsInvDistinct acc)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    MkDeclsInvDistinct acc' := by
  refine ⟨MkDeclsInv_functionStep hP.1 hstep, ?_⟩
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  have hnodup : acc.1.contains function.name = false := by
    cases hc : acc.1.contains function.name with
    | false => rfl
    | true => exfalso; rw [hc] at hstep; simp only [↓reduceIte] at hstep; cases hstep
  rw [hnodup] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  intro k dt hget
  by_cases hkn : (function.name == k) = true
  · exfalso
    have hkEq := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [← hstep] at hget
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [← hstep] at hget
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP.2 k dt hget

private theorem MkDeclsInvDistinct_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {dataType : DataType}
    (hP : MkDeclsInvDistinct acc)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    MkDeclsInvDistinct acc' := by
  have hPnew : MkDeclsInv acc' := MkDeclsInv_dataTypeStep hP.1 hstep
  refine ⟨hPnew, ?_⟩
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  have hnodup_dt : acc.1.contains dataType.name = false := by
    cases hc : acc.1.contains dataType.name with
    | false => rfl
    | true => exfalso; rw [hc] at hstep; simp only [↓reduceIte] at hstep; cases hstep
  rw [hnodup_dt] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  let dt' : DataType := { dataType with constructors }
  intro k dt'' hget
  by_cases hkn : (dataType.name == k) = true
  · -- New dt: dt'' = dt'.
    have hkEq := LawfulBEq.eq_of_beq hkn
    subst hkEq
    have hdt''_eq : dt'' = dt' := by
      have hdt_init : (acc.1.insert dataType.name,
                      acc.2.insert dataType.name (.dataType dt')).2.getByKey dataType.name =
          some (.dataType dt') := IndexMap.getByKey_insert_self _ _ _
      have h := MkDeclsInv_ctor_fold_dt_preserved dataType.name dt' constructors
        _ acc' hdt_init hstep
      rw [h] at hget; cases hget; rfl
    subst hdt''_eq
    -- New dt'.constructors = constructors. Apply ctor_fold_nameHeads_distinct
    -- with ctors_already := [].
    have hres := ctor_fold_nameHeads_distinct dataType.name dt' constructors []
      (acc.1.insert dataType.name, acc.2.insert dataType.name (.dataType dt')) acc'
      (fun _ hc => absurd hc List.not_mem_nil)
      (fun i j hi _ _ => absurd hi (Nat.not_lt_zero _))
      hstep
    intro i j hi hj heq
    -- dt'.constructors = constructors by definition of dt'.
    change i < constructors.length at hi
    change j < constructors.length at hj
    change (constructors[i]'hi).nameHead = (constructors[j]'hj).nameHead at heq
    have hi' : i < ([] ++ constructors).length := by rw [List.nil_append]; exact hi
    have hj' : j < ([] ++ constructors).length := by rw [List.nil_append]; exact hj
    have hgi : ([] ++ constructors)[i]'hi' = constructors[i]'hi := by simp
    have hgj : ([] ++ constructors)[j]'hj' = constructors[j]'hj := by simp
    have heq' : (([] ++ constructors)[i]'hi').nameHead =
        (([] ++ constructors)[j]'hj').nameHead := by
      rw [hgi, hgj]; exact heq
    exact hres i j hi' hj' heq'
  · -- Old dt: k ≠ dataType.name. dt'' was in acc.2 already.
    have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    have hget_acc : acc.2.getByKey k = some (.dataType dt'') := by
      have hk_no_ctor : ∀ c' ∈ constructors,
          (dataType.name.pushNamespace c'.nameHead == k) = false := by
        intro c' hc'
        cases hbeq : (dataType.name.pushNamespace c'.nameHead == k) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hbeq
          have hctor := ctor_fold_inserts_all dataType.name dt' constructors []
            (acc.1.insert dataType.name, acc.2.insert dataType.name (.dataType dt')) acc'
            (MkDeclsInv_dataTypeStep_mid hP.1 hnodup_dt)
            (IndexMap.getByKey_insert_self _ _ _) rfl rfl
            (fun _ hc => absurd hc List.not_mem_nil) hstep c' hc'
          rw [heq] at hctor
          rw [hctor] at hget; cases hget
      have hpres := ctor_fold_preserves_other_key dataType.name dt' constructors
        _ acc' hstep k hk_no_ctor
      rw [hpres] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hget
    exact hP.2 k dt'' hget_acc

private theorem MkDeclsInvDistinct_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    ∃ allNames, MkDeclsInvDistinct (allNames, decls) := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : MkDeclsInvDistinct afterFns := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · exact MkDeclsInvDistinct_default aliasNames
    · intro a x a' _hmem hstep hP
      exact MkDeclsInvDistinct_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  refine ⟨afterDts.1, ?_⟩
  have heq : afterDts = (afterDts.1, afterDts.2) := rfl
  rw [heq]
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' _hmem hstep hP
    exact MkDeclsInvDistinct_dataTypeStep hP hstep

/-- Public: `mkDecls` establishes positional `nameHead` distinctness in every
dt's constructor list. -/
theorem mkDecls_dt_ctor_nameheads_distinct
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt, decls.getByKey k = some (.dataType dt) →
      ∀ i j (hi : i < dt.constructors.length) (hj : j < dt.constructors.length),
        (dt.constructors[i]'hi).nameHead = (dt.constructors[j]'hj).nameHead → i = j := by
  obtain ⟨_, hInv⟩ := MkDeclsInvDistinct_mkDecls hdecls
  exact hInv.2

/-! ## Source-side ctor-key-shape invariant.

Every `.constructor dt c` entry produced by `mkDecls` is stored at the key
`dt.name.pushNamespace c.nameHead`. Reason: the inner ctor fold of
`mkDecls_dataTypeStep` inserts each ctor at exactly that pushed key, and
function/dataType inserts never insert `.constructor` values. -/

/-- Source-side ctor-key-shape predicate. -/
private def MkDeclsCtorKeyShape (decls : Source.Decls) : Prop :=
  ∀ k dt c, decls.getByKey k = some (.constructor dt c) →
    k = dt.name.pushNamespace c.nameHead

private theorem MkDeclsCtorKeyShape_default :
    MkDeclsCtorKeyShape (default : Source.Decls) := by
  intro k dt c hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem MkDeclsCtorKeyShape_insert_function
    {d : Source.Decls} (hP : MkDeclsCtorKeyShape d) (name : Global) (f : Source.Function) :
    MkDeclsCtorKeyShape (d.insert name (.function f)) := by
  intro k dt c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt c hget

private theorem MkDeclsCtorKeyShape_insert_dataType
    {d : Source.Decls} (hP : MkDeclsCtorKeyShape d) (name : Global) (dt : DataType) :
    MkDeclsCtorKeyShape (d.insert name (.dataType dt)) := by
  intro k dt' c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c hget

/-- Insert a ctor at its keyed location preserves the ctor-key-shape. -/
private theorem MkDeclsCtorKeyShape_insert_constructor_at_key
    {d : Source.Decls} (hP : MkDeclsCtorKeyShape d)
    (dt : DataType) (c : Constructor) :
    MkDeclsCtorKeyShape
      (d.insert (dt.name.pushNamespace c.nameHead) (.constructor dt c)) := by
  intro k dt' c' hget
  by_cases hkn : (dt.name.pushNamespace c.nameHead == k) = true
  · have hkEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hget
    obtain ⟨hdtEq, hcEq⟩ := hget
    rw [← hdtEq, ← hcEq]
  · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
      Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c' hget

private theorem MkDeclsCtorKeyShape_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {function : Source.Function}
    (hP : MkDeclsCtorKeyShape acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    MkDeclsCtorKeyShape acc'.2 := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  exact MkDeclsCtorKeyShape_insert_function hP _ _

/-- Inner ctor fold preserves ctor-key-shape: each ctor is inserted at its
pushed key. -/
private theorem MkDeclsCtorKeyShape_ctor_fold
    (dataTypeName : Global) (dataType' : DataType)
    (hname : dataType'.name = dataTypeName) :
    ∀ (ctors : List Constructor) (init result : Std.HashSet Global × Source.Decls),
      MkDeclsCtorKeyShape init.2 →
      ctors.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      MkDeclsCtorKeyShape result.2 := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hP hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro init result hP hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hc
    split at hc
    · exact absurd hc (by intro h; cases h)
    · simp only [Except.ok.injEq] at hc
      subst hc
      apply ih _ result _ hfold
      have hk_eq : dataType'.name.pushNamespace c.nameHead =
          dataTypeName.pushNamespace c.nameHead := by rw [hname]
      have hrewrite : init.2.insert (dataTypeName.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c) =
          init.2.insert (dataType'.name.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c) := by
        rw [hk_eq]
      show MkDeclsCtorKeyShape
        (init.1.insert (dataTypeName.pushNamespace c.nameHead),
          init.2.insert (dataTypeName.pushNamespace c.nameHead)
            (Source.Declaration.constructor dataType' c)).2
      rw [hrewrite]
      exact MkDeclsCtorKeyShape_insert_constructor_at_key hP dataType' c

private theorem MkDeclsCtorKeyShape_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : Std.HashSet Global × Source.Decls} {dataType : DataType}
    (hP : MkDeclsCtorKeyShape acc.2)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    MkDeclsCtorKeyShape acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hP_mid : MkDeclsCtorKeyShape (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    MkDeclsCtorKeyShape_insert_dataType hP dataType.name _
  exact MkDeclsCtorKeyShape_ctor_fold dataType.name { dataType with constructors }
    rfl constructors _ acc' hP_mid hstep

private theorem MkDeclsCtorKeyShape_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    MkDeclsCtorKeyShape decls := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : MkDeclsCtorKeyShape afterFns.2 := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · exact MkDeclsCtorKeyShape_default
    · intro a x a' _hmem hstep hP
      exact MkDeclsCtorKeyShape_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' _hmem hstep hP
    exact MkDeclsCtorKeyShape_dataTypeStep hP hstep

/-- Public: every constructor entry in `mkDecls` output is stored at its
pushed key `dt.name.pushNamespace c.nameHead`. -/
theorem mkDecls_source_ctor_is_key
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt c, decls.getByKey k = some (.constructor dt c) →
      k = dt.name.pushNamespace c.nameHead :=
  MkDeclsCtorKeyShape_mkDecls hdecls

/-! ## Fresh-visited lemma for `wellFormedDecls` fold.

For each `(name, .dataType dt) ∈ decls.pairs.toList`, when we split the
fold at this pair, the visited-state BEFORE processing is fresh for
`dt.name`. Reason: visited only grows by `dt'.name` when a prior
`.dataType dt'` pair was processed, and by IndexMap key-uniqueness +
`SrcDtKeyIsName`, no prior pair has key `dt.name` (since our target pair
has key `name = dt.name`). -/

/-- Single-step growth: `wellFormedDecl` on a non-`.dataType` decl
preserves visited. -/
private theorem wellFormedDecl_non_dt_preserves_visited
    {decls : Source.Decls} {visited visited' : Std.HashSet Global} {d : Source.Declaration}
    (hnotDt : ∀ dt, d ≠ .dataType dt)
    (hstep : wellFormedDecls.wellFormedDecl decls visited d = .ok visited') :
    visited' = visited := by
  cases d with
  | function f =>
    unfold wellFormedDecls.wellFormedDecl at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    exact hstep.symm
  | dataType dt =>
    exact absurd rfl (hnotDt dt)
  | constructor _ _ =>
    unfold wellFormedDecls.wellFormedDecl at hstep
    simp only [pure, Except.pure, Except.ok.injEq] at hstep
    exact hstep.symm

/-- Single-step growth: `.dataType` step inserts at most `dt.name`. -/
private theorem wellFormedDecl_dt_visited_growth
    {decls : Source.Decls} {visited visited' : Std.HashSet Global} {dt : DataType}
    (hstep : wellFormedDecls.wellFormedDecl decls visited (.dataType dt) = .ok visited') :
    visited' = visited ∨ visited' = visited.insert dt.name := by
  unfold wellFormedDecls.wellFormedDecl at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hvis : visited.contains dt.name = true
  · -- visited already contains dt.name: returns .ok visited
    rw [hvis] at hstep
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hstep
    exact .inl hstep.symm
  · -- visited doesn't contain dt.name: returns .ok (visited.insert dt.name)
    have hvis' : visited.contains dt.name = false := Bool.not_eq_true _ |>.mp hvis
    rw [hvis'] at hstep
    simp only [Bool.not_false, ↓reduceIte] at hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    exact .inr hstep.symm

/-- Fold-level visited-source lemma: if `g ∈ final_visited`, then either `g`
was already in init, or there is some earlier pair `(k, .dataType dt)` in
xs with `dt.name = g`. -/
private theorem wellFormedDecls_fold_visited_source
    {decls : Source.Decls} :
    ∀ (xs : List (Global × Source.Declaration)) (init final : Std.HashSet Global),
      xs.foldlM (fun v (_, d) => wellFormedDecls.wellFormedDecl decls v d) init = .ok final →
      ∀ g, final.contains g = true →
        init.contains g = true ∨
        ∃ k dt, (k, Source.Declaration.dataType dt) ∈ xs ∧ dt.name = g := by
  intro xs
  induction xs with
  | nil =>
    intro init final hfold g hg
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold
    exact .inl hg
  | cons hd tl ih =>
    intro init final hfold g hg
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · cases hfold
    rename_i v' hstep
    -- case-split on hd.snd
    obtain ⟨name, d⟩ := hd
    simp only at hstep
    cases d with
    | function f =>
      have hv_eq : v' = init :=
        wellFormedDecl_non_dt_preserves_visited
          (by intro dt h; cases h) hstep
      have ih' := ih v' final hfold g hg
      rw [hv_eq] at ih'
      rcases ih' with h0 | ⟨k', dt, hmem, hname⟩
      · exact .inl h0
      · exact .inr ⟨k', dt, List.mem_cons_of_mem _ hmem, hname⟩
    | dataType dt =>
      have hgrow := wellFormedDecl_dt_visited_growth hstep
      have ih' := ih v' final hfold g hg
      rcases ih' with h0 | ⟨k', dt2, hmem, hname⟩
      · rcases hgrow with hv_eq | hv_eq
        · rw [hv_eq] at h0
          exact .inl h0
        · rw [hv_eq] at h0
          rw [Std.HashSet.contains_insert] at h0
          rcases Bool.or_eq_true .. |>.mp h0 with heq | hin
          · have hnameG : dt.name = g := LawfulBEq.eq_of_beq heq
            refine .inr ⟨name, dt, ?_, hnameG⟩
            exact List.mem_cons_self
          · exact .inl hin
      · exact .inr ⟨k', dt2, List.mem_cons_of_mem _ hmem, hname⟩
    | constructor dt c =>
      have hv_eq : v' = init :=
        wellFormedDecl_non_dt_preserves_visited
          (by intro dt h; cases h) hstep
      have ih' := ih v' final hfold g hg
      rw [hv_eq] at ih'
      rcases ih' with h0 | ⟨k', dt2, hmem, hname⟩
      · exact .inl h0
      · exact .inr ⟨k', dt2, List.mem_cons_of_mem _ hmem, hname⟩

/-- Main reflection: given a source pair `(name, .dataType dt)` in
`decls.pairs.toList` (with `name = dt.name` from `SrcDtKeyIsName`), the
fold processes this pair with a FRESH visited state that doesn't contain
`dt.name`. Returns the per-pair witness with freshness. -/
theorem wellFormedDecls_reflect_dataType_fresh
    {decls : Source.Decls}
    (hdt_key_name : ∀ k dt, decls.getByKey k = some (.dataType dt) → k = dt.name)
    (hwf : wellFormedDecls decls = .ok ())
    {name : Global} {dt : DataType}
    (hmem : (name, Source.Declaration.dataType dt) ∈ decls.pairs.toList) :
    ∃ (visited visited' : Std.HashSet Global),
      visited.contains dt.name = false ∧
      wellFormedDecls.wellFormedDecl decls visited (.dataType dt) = .ok visited' := by
  unfold wellFormedDecls at hwf
  simp only [bind, Except.bind] at hwf
  split at hwf
  · exact absurd hwf (by intro h'; cases h')
  rename_i final hfold
  rw [← Array.foldlM_toList] at hfold
  -- Split `decls.pairs.toList` at our pair.
  obtain ⟨processed, rest, hsplit⟩ := List.append_of_mem hmem
  -- Use `List.foldlM_except_witness_with_context` to get vis_before, vis_after.
  obtain ⟨vis_before, vis_after, hp_ok, hstep_ok, _hrest_ok⟩ :=
    List.foldlM_except_witness_with_context
      (f := fun v (p : Global × Source.Declaration) =>
        wellFormedDecls.wellFormedDecl decls v p.snd)
      decls.pairs.toList _ _ hfold processed (name, .dataType dt) rest hsplit
  refine ⟨vis_before, vis_after, ?_, hstep_ok⟩
  -- Show vis_before.contains dt.name = false by contradiction.
  cases hc : vis_before.contains dt.name with
  | false => rfl
  | true =>
    exfalso
    have hvs := wellFormedDecls_fold_visited_source processed default vis_before hp_ok dt.name hc
    rcases hvs with h0 | ⟨k', dt', hdt'_mem, hdt'_name⟩
    · -- initial visited is default (empty), so dt.name ∉ default
      have hne : (default : Std.HashSet Global).contains dt.name = false := by
        have h_def : (default : Std.HashSet Global) = ({} : Std.HashSet Global) := rfl
        rw [h_def, Std.HashSet.contains_empty]
      rw [hne] at h0; cases h0
    · -- Some earlier pair `(k', .dataType dt')` with dt'.name = dt.name is in
      -- `processed`. Under `hdt_key_name`, we'll derive k' = dt'.name = dt.name.
      -- Our target pair `(name, .dataType dt)` has name = dt.name (same reason).
      -- So both pairs `(dt.name, .dataType dt')` and `(dt.name, .dataType dt)`
      -- appear in `decls.pairs.toList`. By IndexMap key-uniqueness, they're the
      -- same pair, i.e. `dt' = dt`. Then `(name, .dataType dt) ∈ processed`, but
      -- processed ++ [(name, .dataType dt)] ++ rest = decls.pairs.toList. This
      -- would require `(name, .dataType dt)` to appear in `decls.pairs.toList`
      -- TWICE, once in processed and once at the split position. Rule out via
      -- IndexMap key-uniqueness: list pairs with same key are same pair.
      have hprev_in_pairs : (k', Source.Declaration.dataType dt') ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hdt'_mem
      have hk'_eq_dt'name : k' = dt'.name := hdt_key_name k' dt'
        (IndexMap.getByKey_of_mem_pairs _ _ _ hprev_in_pairs)
      have hname_eq_dtname : name = dt.name := hdt_key_name name dt
        (IndexMap.getByKey_of_mem_pairs _ _ _ hmem)
      -- Now: both pairs have key = dt.name.
      have hkey_same : (k' == name) = true := by
        rw [hk'_eq_dt'name, hdt'_name, hname_eq_dtname]
        simp
      have hpair_same := IndexMap.pairs_key_unique _ hprev_in_pairs hmem hkey_same
      -- Now: (k', .dataType dt') = (name, .dataType dt), so hdt'_mem becomes
      -- (name, .dataType dt) ∈ processed.
      rw [hpair_same] at hdt'_mem
      -- `(name, .dataType dt) ∈ processed`. Extract position i < processed.length.
      obtain ⟨i, hi_proc, hi_proc_eq⟩ := List.getElem_of_mem hdt'_mem
      -- Target pair is at position processed.length in the full list.
      have hlen_full : decls.pairs.toList.length = processed.length + (1 + rest.length) := by
        rw [hsplit, List.length_append, List.length_cons]; omega
      have hi_arr : i < decls.pairs.size := by
        rw [show decls.pairs.size = decls.pairs.toList.length
          from (Array.length_toList).symm]
        omega
      have htgt_arr : processed.length < decls.pairs.size := by
        rw [show decls.pairs.size = decls.pairs.toList.length
          from (Array.length_toList).symm]
        omega
      -- Fetch both pairs from the array, equate their first components.
      -- Key move: prove both list-lookups without rewriting the whole list.
      have hfull_i : ∀ (h : i < decls.pairs.toList.length),
          decls.pairs.toList[i]'h = (name, Source.Declaration.dataType dt) := by
        intro h
        have hfl : (processed ++ (name, .dataType dt) :: rest)[i]'(by
            rw [show processed ++ (name, .dataType dt) :: rest = decls.pairs.toList
                from hsplit.symm]; exact h) =
            (name, .dataType dt) := by
          rw [List.getElem_append_left (h := hi_proc)]
          exact hi_proc_eq
        have : decls.pairs.toList[i]'h =
               (processed ++ (name, .dataType dt) :: rest)[i]'(by
                 rw [show processed ++ (name, .dataType dt) :: rest = decls.pairs.toList
                     from hsplit.symm]; exact h) := by
          congr 1
        rw [this, hfl]
      have hfull_tgt : ∀ (h : processed.length < decls.pairs.toList.length),
          decls.pairs.toList[processed.length]'h =
          (name, Source.Declaration.dataType dt) := by
        intro h
        have hfl : (processed ++ (name, .dataType dt) :: rest)[processed.length]'(by
            rw [show processed ++ (name, .dataType dt) :: rest = decls.pairs.toList
                from hsplit.symm]; exact h) =
            (name, .dataType dt) := by
          rw [List.getElem_append_right (by simp)]
          simp
        have : decls.pairs.toList[processed.length]'h =
               (processed ++ (name, .dataType dt) :: rest)[processed.length]'(by
                 rw [show processed ++ (name, .dataType dt) :: rest = decls.pairs.toList
                     from hsplit.symm]; exact h) := by
          congr 1
        rw [this, hfl]
      have hi_full : i < decls.pairs.toList.length := by
        rw [Array.length_toList]; exact hi_arr
      have htgt_full : processed.length < decls.pairs.toList.length := by
        rw [Array.length_toList]; exact htgt_arr
      have harr_i : decls.pairs[i]'hi_arr = (name, Source.Declaration.dataType dt) := by
        have h1 := Array.getElem_toList (xs := decls.pairs) (i := i) (h := hi_arr)
        -- h1 : decls.pairs.toList[i] = decls.pairs[i]
        have h2 : decls.pairs.toList[i]'hi_full = (name, .dataType dt) := hfull_i hi_full
        rw [← h2]; exact h1.symm
      have harr_tgt : decls.pairs[processed.length]'htgt_arr =
          (name, Source.Declaration.dataType dt) := by
        have h1 := Array.getElem_toList (xs := decls.pairs) (i := processed.length) (h := htgt_arr)
        have h2 : decls.pairs.toList[processed.length]'htgt_full = (name, .dataType dt) :=
          hfull_tgt htgt_full
        rw [← h2]; exact h1.symm
      -- Use pairsIndexed invariant to derive i = processed.length.
      have hidx_i := decls.pairsIndexed i hi_arr
      have hidx_tgt := decls.pairsIndexed processed.length htgt_arr
      rw [harr_i] at hidx_i
      rw [harr_tgt] at hidx_tgt
      have heq : (some i : Option Nat) = some processed.length := by
        rw [← hidx_i]; exact hidx_tgt
      have hi_eq_tgt : i = processed.length := Option.some.inj heq
      omega

/-! ## Constructor-in-dt lemma for source decls.

`mkDecls_ctor_companion` gives us that for every `.constructor dt c`
source entry, the companion `.dataType dt` exists at `dt.name` AND
`c ∈ dt.constructors`. This is exactly what we need for the
`.constructor` arm of L1. -/

end Aiur

end
