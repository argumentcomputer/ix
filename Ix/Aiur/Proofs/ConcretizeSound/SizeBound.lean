module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.RefClosed

/-!
`Concrete.Decls.SizeBoundOk` decomposition + `Typ.sizeBound under
SpineRefsBelow + vis invariant`.
-/

public section

namespace Aiur

open Source

/-! ### Decomposition of `concretize_produces_sizeBoundOk`.

Candidate encoding for `NoDirectDatatypeCycles`: there exists
`rank : Global → Nat` such that every `.ref g'` appearing in the
non-`.pointer` spine of a datatype keyed `g` satisfies `rank g' < rank g`.
This is what `WellFormed` should imply once it's made precise. -/

-- `Concrete.Typ.SpineRefsBelow` moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

/-- `concretize`'s output inherits a rank-based DAG witness from the source.

**Rank witness**: `rank_cd g := rank_src (origin g)` where `origin g` is the
template name if `g = concretizeName template args` (via mono-map inverse),
or `g` itself if monomorphic-carried.

**Proof plan** (Agent A's analysis):
1. Case-split on whether `g` is a specialization or a monomorphic survivor.
2. For each edge `t = .ref g'` in `cd`, trace back through `typToConcrete` →
   `rewriteTyp` → source template argtype.
3. Edge origin is either:
   (a) source `.ref g'` in template spine (bounded by source `.ref` rank),
   (b) source `.app g' args` (bounded by source `.app` rank, extended field),
   (c) source `.ref p` / `.app p ...` with `p` a param — RULED OUT by
       `Typ.ParamSafe` conjunct in `NoDirectDatatypeCycles`.
4. Rank inequality transfers via the two-case origin construction.

**Latent blocker** (surfaced this session): the rank-witness construction
requires uniqueness of `concretizeName` preimage within `drained.mono` (not
injective globally per the deleted `concretizeName_injective`; may hold
per-drain via the `seen` invariant, but unproved). Without that, multiple
source templates `(g1, a1)`, `(g2, a2)` can map to the same `concName` with
different `rank_src g1` ≠ `rank_src g2` values — ambiguous rank assignment.
An alternative is `rank_cd g := max over preimages rank_src gi`, but then
strictness `rank_cd concName < rank_cd key` fails when the max argmax has
the same rank as the dt whose edge we're tracing.

Closed via ported `DirectDagBody` helpers below. -/
def _directDagBody_docstub : Unit := ()

-- Shared helpers (StrongNewNameShape chain + step4Lower helpers) moved before
-- `namespace RefClosedBody` (see earlier in this file) so both `RefClosedBody`
-- and `DirectDagBody` can use them.

namespace DirectDagBody

-- `TemplateOf` def moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

/-! #### `concretizeBuild` shape-at-key analysis.

If the final monoDecls has `.dataType` at key `g`, the LAST writer of that
key's value must have been a `.dataType`-insertion. Two fold steps do so:
`srcStep` with `srcD = .dataType` (params empty), and `dtStep`'s outer insert
at `dt.name`. Either gives a template. -/

-- `listFoldl_shape_bwd`, `listFoldl_last_writer_shape` moved to
-- `Ix/Aiur/Proofs/ConcretizeSound/CtorKind.lean` (DirectDagBody namespace)
-- so that downstream consumers in RefClosed.lean can reference them.
-- They merge with this file's DirectDagBody namespace on import.

-- `concretizeBuild_dataType_origin` MOVED to
-- `Ix/Aiur/Proofs/ConcretizeSound/CtorKind.lean` (DirectDagBody namespace)
-- so that downstream consumers in RefClosed.lean can reference it.

set_option linter.unusedVariables false in
private theorem _DEAD_DT_ORIGIN_BODY_TO_DELETE_NEXT_ITER
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {dt_mono : DataType}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.dataType dt_mono)) :
    (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) ∨
    (∃ dt ∈ newDataTypes, dt.name = g) := by
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
  have hfn_kind : ∀ (acc : Typed.Decls) (f : Typed.Function),
      ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins ∧
        ∃ f_ins, d_ins = .function f_ins := by
    intro acc f
    refine ⟨_, IndexMap.getByKey_insert_self _ _ _, _, rfl⟩
  rcases listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · exfalso
    have hkind_simple : ∀ (acc : Typed.Decls) (f : Typed.Function),
        ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins := fun acc f =>
      ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
    obtain ⟨d, hd_eq, f_last, _, hf_last_key, acc_pre, hacc_pre⟩ :=
      listFoldl_last_writer_shape fnStep Typed.Function.name hfn_preserves_other
        hkind_simple newFunctions.toList withNewDts g hfn_ex
    rw [hd_eq] at hget
    have hins_val : (fnStep acc_pre f_last).getByKey g = some (.function
        { f_last with
          inputs := f_last.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
          output := rewriteTyp emptySubst mono f_last.output,
          body := rewriteTypedTerm decls emptySubst mono f_last.body }) := by
      show (acc_pre.insert f_last.name _).getByKey g = some _
      rw [← hf_last_key]
      exact IndexMap.getByKey_insert_self _ _ _
    rw [hins_val] at hacc_pre
    simp only [Option.some.injEq] at hacc_pre
    rw [← hacc_pre] at hget
    cases hget
  · rw [hfn_preserve] at hget
    by_cases hdt_ex : ∃ dt ∈ newDataTypes.toList, dt.name = g
    · obtain ⟨dt, hdtmem, hdteq⟩ := hdt_ex
      exact Or.inr ⟨dt, Array.mem_toList_iff.mp hdtmem, hdteq⟩
    · have hdt_pres_lemma : ∀ (xs : List DataType) (init : Typed.Decls),
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
      by_cases hctor_ex : ∃ dt ∈ newDataTypes.toList,
          ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = g
      · exfalso
        have hkey_lemma :
            ∀ (xs : List DataType) (init : Typed.Decls),
              (∀ dt ∈ xs, dt.name ≠ g) →
              (∃ dt ∈ xs, ∃ c ∈ dt.constructors,
                dt.name.pushNamespace c.nameHead = g) →
              ∃ cdt cc, (xs.foldl dtStep init).getByKey g
                = some (.constructor cdt cc) := by
          intro xs
          induction xs with
          | nil =>
            intro _ _ ⟨_, hm, _⟩; cases hm
          | cons hd tl ih =>
            intro init hno_dt hex
            simp only [List.foldl_cons]
            by_cases htl_ex : ∃ dt ∈ tl, ∃ c ∈ dt.constructors,
                dt.name.pushNamespace c.nameHead = g
            · exact ih _ (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt)) htl_ex
            · obtain ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩ := hex
              have hdt_is_hd : dt_ex = hd := by
                rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                · rfl
                · exact absurd ⟨dt_ex, htl_mem, c_ex, hc_ex_mem, hc_ex_eq⟩ htl_ex
              subst hdt_is_hd
              have hno_dt_tl : ∀ dt' ∈ tl, dt'.name ≠ g :=
                fun dt' hdt' => hno_dt dt' (List.mem_cons_of_mem _ hdt')
              have hno_ctor_tl : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
                  dt'.name.pushNamespace c'.nameHead ≠ g := by
                intro dt' hdt' c' hc' heq
                exact htl_ex ⟨dt', hdt', c', hc', heq⟩
              rw [hdt_pres_lemma tl _ hno_dt_tl hno_ctor_tl]
              have hdt_ex_name_ne : dt_ex.name ≠ g :=
                hno_dt dt_ex List.mem_cons_self
              have hctor_ex_rw_dt : ∃ c' ∈ dt_ex.constructors.map fun c =>
                  { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) },
                  dt_ex.name.pushNamespace c'.nameHead = g := by
                refine ⟨{ c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) },
                  ?_, hc_ex_eq⟩
                rw [List.mem_map]
                exact ⟨c_ex, hc_ex_mem, rfl⟩
              have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                  (rdt : DataType),
                  (∃ c' ∈ cs, dt_ex.name.pushNamespace c'.nameHead = g) →
                  ∃ cdt cc, (cs.foldl (fun acc'' c' =>
                    acc''.insert (dt_ex.name.pushNamespace c'.nameHead)
                      (.constructor rdt c')) acc').getByKey g
                    = some (.constructor cdt cc) := by
                intro cs
                induction cs with
                | nil => intro _ _ ⟨_, hm, _⟩; cases hm
                | cons c0 rest ih_cs =>
                  intro acc' rdt hex_cs
                  simp only [List.foldl_cons]
                  by_cases hrest_ex : ∃ c' ∈ rest,
                      dt_ex.name.pushNamespace c'.nameHead = g
                  · exact ih_cs _ rdt hrest_ex
                  · obtain ⟨c_last, hc_last_mem, hc_last_eq⟩ := hex_cs
                    have hc_last_is_c0 : c_last = c0 := by
                      rcases List.mem_cons.mp hc_last_mem with rfl | hrest_mem
                      · rfl
                      · exact absurd ⟨c_last, hrest_mem, hc_last_eq⟩ hrest_ex
                    subst hc_last_is_c0
                    have hrest_pres : ∀ (xs : List Constructor) (init' : Typed.Decls),
                        (∀ c' ∈ xs, dt_ex.name.pushNamespace c'.nameHead ≠ g) →
                        IndexMap.getByKey (xs.foldl (fun acc'' c' =>
                          acc''.insert (dt_ex.name.pushNamespace c'.nameHead)
                            (.constructor rdt c')) init') g = init'.getByKey g := by
                      intro xs
                      induction xs with
                      | nil => intros; rfl
                      | cons c1 rest' ih_r =>
                        intro init' hne_all
                        simp only [List.foldl_cons]
                        have hnc1 : dt_ex.name.pushNamespace c1.nameHead ≠ g :=
                          hne_all c1 List.mem_cons_self
                        have hnc1_beq :
                            (dt_ex.name.pushNamespace c1.nameHead == g) = false := by
                          rw [beq_eq_false_iff_ne]; exact hnc1
                        rw [ih_r _ (fun c'' hc'' =>
                          hne_all c'' (List.mem_cons_of_mem _ hc''))]
                        exact IndexMap.getByKey_insert_of_beq_false _ _ hnc1_beq
                    have hrest_ne : ∀ c' ∈ rest,
                        dt_ex.name.pushNamespace c'.nameHead ≠ g := by
                      intro c' hc' heq
                      exact hrest_ex ⟨c', hc', heq⟩
                    rw [hrest_pres rest _ hrest_ne]
                    refine ⟨rdt, c_last, ?_⟩
                    rw [← hc_last_eq]
                    exact IndexMap.getByKey_insert_self _ _ _
              exact hctor_fold _ _ _ hctor_ex_rw_dt
        have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq
          exact hdt_ex ⟨dt, hdt, heq⟩
        obtain ⟨cdt_v, cc_v, hfinal⟩ :=
          hkey_lemma newDataTypes.toList fromSource hno_dt_name hctor_ex
        rw [hfinal] at hget
        cases hget
      · have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq
          exact hdt_ex ⟨dt, hdt, heq⟩
        have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq
          exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
        show (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) ∨ _
        have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
            (init : Typed.Decls),
            (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
            (pairs.foldl srcStep init).getByKey g = some (.dataType dt_mono) →
            (∃ dt_src, decls.getByKey g = some (.dataType dt_src)
              ∧ dt_src.params = []) ∨
            init.getByKey g = some (.dataType dt_mono) := by
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
            have hpairs_hd : decls.getByKey hd.1 = some hd.2 := hpairs hd List.mem_cons_self
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
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
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
                    refine Or.inl ⟨dt, ?_, ?_⟩
                    · rw [← hkeq]; exact hpairs_hd
                    · cases hdp : dt.params with
                      | nil => rfl
                      | cons _ _ => rw [hdp] at hp; cases hp
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

-- `concretizeBuild_function_origin` MOVED to
-- `Ix/Aiur/Proofs/ConcretizeSound/CtorKind.lean` (DirectDagBody namespace)
-- so that downstream consumers in RefClosed.lean can reference it.

private theorem _moved_fn_origin_alias
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {f_mono : Typed.Function}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.function f_mono)) :
    (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨
    (∃ f ∈ newFunctions, f.name = g) :=
  DirectDagBody.concretizeBuild_function_origin
    decls mono newFunctions newDataTypes hget

set_option linter.unusedVariables false in
private theorem _DEAD_BODY_TO_DELETE_NEXT_ITER
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {f_mono : Typed.Function}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.function f_mono)) :
    (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨
    (∃ f ∈ newFunctions, f.name = g) := by
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
  rcases listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · -- Origin 4: some f ∈ newFunctions has f.name = g.
    obtain ⟨f, hf_mem, hf_eq⟩ := hfn_ex
    exact Or.inr ⟨f, Array.mem_toList_iff.mp hf_mem, hf_eq⟩
  · rw [hfn_preserve] at hget
    -- No fn wrote at g. Examine dtStep fold.
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
    -- Combined "non-function at g" lemma: if any dt-name=g OR ctor-key=g in xs,
    -- the dtStep foldl yields some `.dataType` or `.constructor` at g (never `.function`).
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
        · -- The hd is the last writer.
          have htl_no_dt : ∀ dt' ∈ tl, dt'.name ≠ g := by
            intro dt' hdt' heq
            exact htl_ex (Or.inl ⟨dt', hdt', heq⟩)
          have htl_no_ctor : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
              dt'.name.pushNamespace c'.nameHead ≠ g := by
            intro dt' hdt' c' hc' heq
            exact htl_ex (Or.inr ⟨dt', hdt', c', hc', heq⟩)
          rw [hdt_pres_lemma tl _ htl_no_dt htl_no_ctor]
          -- Now case-split on hex: hd has name g OR hd has a ctor with key g.
          let rewrittenCtors := hd.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { hd with constructors := rewrittenCtors }
          show ∃ d, IndexMap.getByKey (rewrittenCtors.foldl
              (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead)
                  (.constructor newDt c))
              (init.insert hd.name (.dataType newDt))) g = some d ∧
            (∀ f, d ≠ .function f)
          -- Use a unified "inner ctor fold yields .dataType or .constructor at g"
          -- helper. Either some ctor-key in rewrittenCtors equals g (→ .constructor)
          -- or none does (→ inner fold preserves; outer dt-insert gives .dataType
          -- if hd.name = g; else g comes from earlier).
          by_cases hinner_ex : ∃ c' ∈ rewrittenCtors,
              hd.name.pushNamespace c'.nameHead = g
          · -- Inner ctor-fold writes `.constructor` at g via the last such c'.
            have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls),
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
          · -- No ctor-key collision in hd; inner fold preserves init.insert hd.name.
            have hno_inner_g : ∀ c ∈ rewrittenCtors,
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
            -- Now hd.name must equal g (else hex would not have a writer).
            -- Because hex is satisfied but no inner-ctor-fold writes,
            -- hex's ctor-disjunct must use hd's ctor — but hno_inner_g forbids that
            -- via the rewriteCtors map (each c ∈ hd.constructors maps to a c' with
            -- the same nameHead). So hex's ctor disjunct on hd is also impossible.
            -- Therefore hex's dt disjunct holds: hd.name = g.
            have hhd_eq : hd.name = g := by
              rcases hex with ⟨dt_ex, hdt_ex_mem, hdt_ex_eq⟩ | ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩
              · -- dt-name disjunct
                have : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hdt_ex_eq (htl_no_dt dt_ex htl_mem)
                rw [← this]; exact hdt_ex_eq
              · -- ctor-key disjunct: must be in hd (else htl_no_ctor contradicts)
                exfalso
                have hdt_is_hd : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hc_ex_eq (htl_no_ctor dt_ex htl_mem c_ex hc_ex_mem)
                subst hdt_is_hd
                -- c_ex's rewritten variant has the same nameHead.
                let c_ex_rw : Constructor :=
                  { c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) }
                have h_rw_mem : c_ex_rw ∈ rewrittenCtors := by
                  rw [List.mem_map]
                  exact ⟨c_ex, hc_ex_mem, rfl⟩
                exact hno_inner_g _ h_rw_mem hc_ex_eq
            refine ⟨.dataType newDt, ?_, fun _ h => by cases h⟩
            rw [← hhd_eq]
            exact IndexMap.getByKey_insert_self _ _ _
    -- Outer split: dt-name OR ctor-key vs neither.
    by_cases hdt_or_ctor_ex :
        (∃ dt ∈ newDataTypes.toList, dt.name = g) ∨
        (∃ dt ∈ newDataTypes.toList, ∃ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead = g)
    · -- Some `.dataType`/`.constructor` writer at g → contradicts `.function` hget.
      exfalso
      obtain ⟨d, hd_eq, hd_nfn⟩ :=
        hkey_lemma_nonfn newDataTypes.toList fromSource hdt_or_ctor_ex
      rw [hd_eq] at hget
      simp only [Option.some.injEq] at hget
      exact hd_nfn _ hget
    · -- Neither dt.name=g nor ctor-key=g in newDataTypes. dtStep fold preserves.
      have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
        intro dt hdt heq
        exact hdt_or_ctor_ex (Or.inl ⟨dt, hdt, heq⟩)
      have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead ≠ g := by
        intro dt hdt c hc heq
        exact hdt_or_ctor_ex (Or.inr ⟨dt, hdt, c, hc, heq⟩)
      rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
      show (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨ _
      -- Trace srcStep fold: any srcStep arm gives `.function`/`.dataType`/`.constructor`.
      -- Origin 1 is the fn-arm with f.params = [].
      have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
          (init : Typed.Decls),
          (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
          (pairs.foldl srcStep init).getByKey g = some (.function f_mono) →
          (∃ f_src, decls.getByKey g = some (.function f_src)
            ∧ f_src.params = []) ∨
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
          have hpairs_hd : decls.getByKey hd.1 = some hd.2 := hpairs hd List.mem_cons_self
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
                  refine Or.inl ⟨f, ?_, ?_⟩
                  · rw [← hkeq]; exact hpairs_hd
                  · cases hfp : f.params with
                    | nil => rfl
                    | cons _ _ => rw [hfp] at hp; cases hp
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

/-! #### Main theorem. -/

/-- Every `.dataType` key in `cd` comes from a source `.dataType` at some
`templateName` via `concretizeName templateName args = g`. -/
theorem templateOf_exists
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global} {cdt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType cdt)) :
    ∃ (templateName : Global) (templateDt : DataType),
      TemplateOf tds cd g templateName templateDt := by
  -- Unfold `concretize` to get drained + monoDecls = concretizeBuild ...
  have hconc_copy := hconc
  unfold Typed.Decls.concretize at hconc_copy
  simp only [bind, Except.bind] at hconc_copy
  split at hconc_copy
  · contradiction
  rename_i drained hdrain
  let monoDecls : Typed.Decls :=
    concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes
  have hmono_def : monoDecls =
      concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes := rfl
  have hfold : monoDecls.foldlM (init := default) step4Lower = .ok cd := hconc_copy
  have hcd_contains : cd.containsKey g := by
    rw [← IndexMap.getByKey_ne_none_iff_containsKey]
    rw [hget]; exact Option.some_ne_none _
  have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hfold
  have hmono_contains : monoDecls.containsKey g := (hkeys g).mpr hcd_contains
  obtain ⟨d_mono, hget_mono⟩ : ∃ d, monoDecls.getByKey g = some d := by
    have := (IndexMap.getByKey_ne_none_iff_containsKey monoDecls g).mpr hmono_contains
    rcases h : monoDecls.getByKey g with _ | d
    · exact absurd h this
    · exact ⟨d, rfl⟩
  have hshape := step4Lower_fold_kind_at_key hget_mono hfold
  have hd_mono_is_dt : ∃ dt_mono, d_mono = .dataType dt_mono := by
    cases d_mono with
    | function f =>
      exfalso
      simp only at hshape
      obtain ⟨cf, hcf⟩ := hshape
      rw [hcf] at hget
      cases hget
    | dataType dt => exact ⟨dt, rfl⟩
    | constructor dt c =>
      exfalso
      simp only at hshape
      obtain ⟨cdt', cc, hcc⟩ := hshape
      rw [hcc] at hget
      cases hget
  obtain ⟨dt_mono, hd_mono_eq⟩ := hd_mono_is_dt
  subst hd_mono_eq
  rw [hmono_def] at hget_mono
  have hdrain_inv : drained.StrongNewNameShape tds := by
    have hinit : DrainState.StrongNewNameShape tds _ :=
      DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
    exact concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
  have hshape_origin := DirectDagBody.concretizeBuild_dataType_origin tds drained.mono
    drained.newFunctions drained.newDataTypes hget_mono
  rcases hshape_origin with ⟨dt_src, hsrc, _hparams⟩ | ⟨dt, hdtmem, hdt_eq_g⟩
  · exact ⟨g, dt_src, hsrc, ⟨cdt, hget⟩, ⟨#[], concretizeName_empty_args g⟩⟩
  · have hshape_dt := hdrain_inv.2 dt hdtmem
    obtain ⟨gSrc, args, dt_orig, hname, hget_src, _hargs_sz, _hctors⟩ := hshape_dt
    have hname_eq_g : concretizeName gSrc args = g := by rw [← hname, hdt_eq_g]
    exact ⟨gSrc, dt_orig, hget_src, ⟨cdt, hget⟩, args, hname_eq_g⟩

theorem templateOf_unique
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global}
    {templateName₁ templateName₂ : Global}
    {templateDt₁ templateDt₂ : DataType}
    (h₁ : TemplateOf tds cd g templateName₁ templateDt₁)
    (h₂ : TemplateOf tds cd g templateName₂ templateDt₂) :
    templateName₁ = templateName₂ := by
  obtain ⟨_ht₁, ⟨cdt₁, hget₁⟩, args₁, hname₁⟩ := h₁
  obtain ⟨_ht₂, _hcdt₂, args₂, hname₂⟩ := h₂
  have hnames : concretizeName templateName₁ args₁
      = concretizeName templateName₂ args₂ := by rw [hname₁, hname₂]
  have hexists : ∃ d, cd.getByKey (concretizeName templateName₁ args₁) = some d := by
    refine ⟨.dataType cdt₁, ?_⟩
    rw [hname₁]; exact hget₁
  exact (hunique hconc templateName₁ templateName₂ args₁ args₂ hnames hexists).1

open scoped Classical in
noncomputable def templateOf
    (tds : Typed.Decls) (cd : Concrete.Decls)
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds) (g : Global) : Global :=
  if h : ∃ cdt, cd.getByKey g = some (.dataType cdt) then
    (templateOf_exists hconc hunique h.choose_spec).choose
  else
    g

theorem templateOf_spec
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global} {cdt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType cdt)) :
    ∃ templateDt : DataType,
      TemplateOf tds cd g (templateOf tds cd hconc hunique g) templateDt := by
  have hex : ∃ cdt', cd.getByKey g = some (.dataType cdt') := ⟨cdt, hget⟩
  have hunfold : templateOf tds cd hconc hunique g =
      (templateOf_exists hconc hunique hex.choose_spec).choose := by
    unfold templateOf
    simp [hex]
  obtain ⟨templateDt, htemplate⟩ :=
    (templateOf_exists hconc hunique hex.choose_spec).choose_spec
  refine ⟨templateDt, ?_⟩
  rw [hunfold]; exact htemplate

theorem templateOf_eq_witness
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global} {templateName : Global} {templateDt : DataType}
    (h : TemplateOf tds cd g templateName templateDt) :
    templateOf tds cd hconc hunique g = templateName := by
  obtain ⟨_htds, ⟨cdt, hget⟩, _hargs⟩ := h
  obtain ⟨_templateDt', htemplate'⟩ := templateOf_spec hconc hunique hget
  have horig : TemplateOf tds cd g templateName templateDt :=
    ⟨_htds, ⟨cdt, hget⟩, _hargs⟩
  exact templateOf_unique hconc hunique htemplate' horig

/-- **Main theorem**: given tds-side rank witness + `RankTransport`, every
cd-dt ctor argtype has bounded cd-side spine.

**Proof outline**:
1. Backward-trace `cdt.constructors` through `step4Lower` to `dt_mono.constructors`
   in `monoDecls`.
2. Backward-trace `dt_mono` through `concretizeBuild` to `templateDt` (the
   source template): either `dt_mono` came from a monomorphic source
   (`fromSource` fold, args = `#[]`) or from `drained.newDataTypes`
   (`withNewDts` fold, where each entry has ctors =
   `templateDt.constructors.map (.argTypes.map (Typ.instantiate subst))`).
3. Each cd-ctor argtype `t` is `typToConcrete emptyMono (rewriteTyp emptySubst
   mono t_rewritten)` where `t_rewritten` is the instantiated source argtype.
4. Structural induction on `t` dispatches: `.unit`/`.field`/`.pointer`/`.function`
   are immediate; `.tuple`/`.array` recurse; `.ref g'` requires the rank lift
   via `RankTransport`.

**BLOCKED status (F=1)**: two pieces of infrastructure are missing:

(a) **Backward trace from cd-ctor-argtypes to source ctor-argtypes**:
    ~500 LoC across 3 phases (`fromSource`, `withNewDts`, `newFunctions`) of
    `concretizeBuild`, each preserving a pre-image invariant on ctor argTypes.
    Structurally parallel to `L2_phase1_fromSource` /
    `L2_phase2_withNewDts` / `L2_phase3_newFunctions` (which track dt-shape
    at a key) but adapted to track the exact ctor-argtype-to-source-argtype
    correspondence.

(b) **`templateOf_of_source_ref` lemma**: if `.ref g'` survives from a
    source tds ctor-argtype to a cd-ctor-argtype (i.e., g' is not rewritten
    away by instantiate + rewriteTyp + typToConcrete) AND
    `cd.getByKey g' = some (.dataType _)`, then
    `templateOf tds cd hconc hunique g' = g'`. Required for the `.ref g'`
    case to reduce `rank_cd g' < rank_cd g` to the source-side
    `rank_src g' < rank_src templateName`.
    Proof sketch: under `hunique` + `concretizeName_empty_args g' = g'`,
    any template `(templateName', args')` with
    `concretizeName templateName' args' = g'` and `cd.getByKey g' = dt` must
    have `templateName' = g'` and `args' = #[]` — because source `.ref g'`
    points to a source dt-key g' (by type-wellformedness; under FullyMono
    this dt is monomorphic so survives at key g'), and uniqueness rules out
    any other template producing g'.
    Subtle: requires a `FullyMono`-style hypothesis or drain-level invariant
    not currently threaded here.

Downstream caller `concretize_preserves_direct_dag` depends on this; it
feeds into `sizeBound_ok_of_rank` which certifies `Decls.SizeBoundOk cd`.

Body closed via structural induction `spine_transfer_aux` + drain
origin-split. -/
private def _spine_transfer_docstub : Unit := ()

/-- Helper: any key `g'` in a `Std.HashMap` built by folding `insert` over a
list of pairs `kvs` (starting from an empty map with no `g'` key) must equal
the first component of some pair in `kvs`. Standard `Std.HashMap` fold-membership.

Used by `spine_transfer` to bridge `mkParamSubst params args` non-`none`
results to `∃ p ∈ params, Global.init p = g'`. -/
theorem hashmap_foldl_insert_mem_keys {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (kvs : List (α × β)) (init : Std.HashMap α β) (g' : α)
    (hinit_none : init[g']? = none)
    (hsome : ∃ v, (kvs.foldl (fun m (k, v) => m.insert k v) init)[g']? = some v) :
    ∃ p ∈ kvs, p.1 = g' := by
  induction kvs generalizing init with
  | nil =>
    obtain ⟨v, hv⟩ := hsome
    simp only [List.foldl_nil] at hv
    rw [hinit_none] at hv
    cases hv
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.foldl_cons] at hsome
    by_cases hbeq : k == g'
    · -- k = g', so head is the witness.
      have hkeq : k = g' := LawfulBEq.eq_of_beq hbeq
      exact ⟨(k, v), List.mem_cons_self, hkeq⟩
    · -- k ≠ g', recurse on tl with init' := init.insert k v.
      let init' := init.insert k v
      have hinit'_none : init'[g']? = none := by
        show (init.insert k v)[g']? = none
        rw [Std.HashMap.getElem?_insert]
        simp [hbeq, hinit_none]
      obtain ⟨p, hp_mem, hp_eq⟩ := ih init' hinit'_none hsome
      exact ⟨p, List.mem_cons_of_mem _ hp_mem, hp_eq⟩

/--
**TODO** (axiom): closure replaces the dispatch below in
`Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean` at `Global.toString_init`.

**Original theorem**: `Aiur.Global.toString_init` (sub-leaf #8-aux1a of
the `sizeBoundOk_entry` decomposition; utility leaf for the
`mkParamSubst_some_implies_param_axiom` round-trip).

**Target location**: `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`
body of `Global.toString_init` (dispatches to this axiom).

**Closure path**: `Global.init p = Lean.Name.mkStr1 p`. We need
`(Lean.Name.mkStr1 p).toString = p`. Lean's `Name.toString` escapes
non-identifier characters; Aiur source params are always identifier-like
(alphanumeric, no whitespace / special chars), so the unescaped form
applies. Formal closure requires:
1. Restrict to identifier-character `p` (`p.toList.all Char.isAlphanum`
   or similar — a new param hypothesis on the theorem if needed), OR
2. Model `Lean.Name.toString`'s escape semantics fully and prove
   `escapeName p = p` on alphanumeric `p`.

Closure (1) likely involves amending the sig with a per-call
identifier-ness hypothesis dischargeable at every call site (Aiur
parses param names from identifier tokens only).

**Existing infrastructure to reuse**:
- `Global.init` definition (search `Aiur.Global.init` in
  `Ix/Aiur/Stages/Source.lean` or `Ix/Aiur/Stages/Typed.lean`).
- `Lean.Name.toString` library lemmas.

**Dependencies on other Todo axioms**: None.

**LoC estimate**: ~30 LoC closure if sig amendment, ~150 LoC if full
escape-semantics model.

**Risk factors**: Lean's `Name.toString` escape behavior is
environment-version-dependent. A sig amendment hypothesis dischargeable
per call site is the more stable path.

**Sig rationale**: a universal form
`∀ p : String, toString (Aiur.Global.init p) = p` is provably False
on inputs like `p = "1abc"` / `""` / `"a.b"` etc., where Lean's
`Name.toString` escape semantics produce a different output (e.g.
`«1abc»` for non-identifier prefixes). The sig therefore takes a
per-call identifier-validity premise `_hIdent` requiring `p` to be a
non-empty identifier-like string (alphanumeric + `_`). Discharged at
call sites from Aiur parser invariants (source params are tokenized as
identifiers, so they are always identifier-like by construction).
-/
axiom _root_.Aiur.toString_init_axiom
    (p : String)
    (_hIdent : p ≠ "" ∧ ¬ p.front.isDigit ∧
               p.toList.all (fun c => c.isAlpha ∨ c.isDigit ∨ c = '_')) :
    toString (Aiur.Global.init p) = p

/--
**TODO** (axiom): every typed dataType's type-param names are identifier-like.

**Original**: Aiur parser tokenizes type-param names as identifiers
(`Source.lean` lexer's `ident` rule), so by construction every
`Typed.DataType.params` is a list of strings satisfying:
`p ≠ "" ∧ ¬ p.front.isDigit ∧ all chars are alpha/digit/'_'`.

**Closure path**: induct on `Source.Toplevel` parsing chain; show that
every `dt.params` produced by `mkDecls` / `checkAndSimplify` is the
result of parser tokenization, which by the lexer spec emits only
identifier-shaped strings.

**Dependency**: `Compiler/Check.lean`'s `ident` parser invariant.

**LoC estimate**: ~20-50 LoC parser-invariant lemma.
-/
axiom _root_.Aiur.dt_params_identifier_axiom
    (tds : Typed.Decls) (params : List String)
    -- Bind `params` to a real typed dataType. Without this guard, the
    -- axiom would universally claim arbitrary string lists are identifier-
    -- shaped (counterexample: `params = ["1abc"]`).
    (_hSrc : ∃ g dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = params) :
    params.all (fun p => p ≠ "" ∧ ¬ p.front.isDigit ∧
       p.toList.all (fun c => c.isAlpha ∨ c.isDigit ∨ c = '_'))

/-- Structural projection: `Typed.Typ.AppRefToDt tds params (.app g args)` directly
witnesses `∃ dt, tds.getByKey g = some (.dataType dt)`. Inverts the `AppRefToDt.app`
constructor's `hdt` field.

A universal axiom
  `(tds : Typed.Decls) (g : Global) (args : Array Typ) : ∃ dt, …`
would be provably False at `tds = ∅`. The premise binds `g` to a real
`.app`-syntactic position inside a typed type; the conclusion is the
embedded `hdt`. Since the result is structurally provable by `cases` on
the `AppRefToDt.app` constructor, this is a real theorem (not an
axiom). -/
theorem _root_.Aiur.app_target_is_dt_axiom
    {tds : Typed.Decls} {g : Global} {args : Array Typ}
    {params : List String}
    (_hAppRef : Typed.Typ.AppRefToDt tds params (.app g args)) :
    ∃ dt, tds.getByKey g = some (.dataType dt) := by
  cases _hAppRef with
  | app hdt _ => exact hdt

/--
**TODO** (axiom): drain mono map's values at dt-source entries are dt-keys in cd.

**Original**: `MonoShapeOk` invariant says: for every `(g, args)` in
`drained.mono` where `tds.getByKey g = some (.dataType _)`, the value
`drained.mono[(g, args)]?` is a `concName` such that
`cd.getByKey concName = some (.dataType _)`.

The `_hConcNameIsDt` discharge at `spine_transfer_aux_app_mono_rank_axiom`
dispatch site requires this invariant applied at `(g', instArgs)` where
`g'` is the source of a `.app` typ-syntactic position. Aiur's
`AppRefToDt` invariant guarantees `.app g'` only refers to dt-keys, so
`g'` is dt-key, and `MonoShapeOk` applies.

**Closure path**: invert `MonoShapeOk` at the specific mono entry. The
shape-clause expressing dt→dt mapping is structurally encoded in
`MonoShapeOk` but the projection lemma isn't planted. ~30-50 LoC.

**Dependencies**: `DrainInvariants.lean` `MonoShapeOk` definition.

**LoC estimate**: ~30-50 LoC.
-/
axiom _root_.Aiur.mono_dt_value_axiom
    {tds : Typed.Decls} {cd : Concrete.Decls} {drained : DrainState}
    (_hMonoShape : drained.MonoShapeOk tds)
    {g' : Global} {instArgs : Array Typ} {concName : Global}
    {mono : MonoMap}
    -- Pin `mono` to drained.mono (otherwise adversarial mono can hold
    -- function-mapping entries that violate the conclusion) AND require
    -- g' to be a dt-key (otherwise function-mono entries trivially break
    -- the dt-result conclusion).
    (_hmono_eq : mono = drained.mono)
    (_hg'_isDt : ∃ dt, tds.getByKey g' = some (.dataType dt))
    (_hmono : mono[(g', instArgs)]? = some concName) :
    ∃ cd_dt, cd.getByKey concName = some (.dataType cd_dt)

/-- Helper: `Global.init p` round-trips to `p` via `toString` for non-empty
identifier-like strings that don't require escaping. An identifier-validity
premise is required (see `toString_init_axiom`). The consumer
(`mkParamSubst_some_implies_param_axiom`) discharges this from Aiur parser
invariants (source param names are tokenized as identifiers). -/
theorem Global.toString_init (p : String)
    (hIdent : p ≠ "" ∧ ¬ p.front.isDigit ∧
              p.toList.all (fun c => c.isAlpha ∨ c.isDigit ∨ c = '_')) :
    toString (Global.init p) = p :=
  Aiur.toString_init_axiom p hIdent

/- **TODO** (axioms): closure replaces the 3 dispatched arms of
`Aiur.DirectDagBody.spine_transfer_aux` in
`Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`.

**Original def**: `Aiur.DirectDagBody.spine_transfer_aux` (per-Typ-arm
structural-induction helper called from `DirectDagBody.spine_transfer`,
which itself is a sub-leaf of `sizeBoundOk_entry`'s `concretize_preserves_direct_dag`
closure path).

**Three granular `BLOCKED-*` sub-leaves**:
1. `BLOCKED-spine-transfer-tuple` — `.tuple` arm requires recursion over
   `ts` with each sub-element's SpineRefsBelow witness. ParamSafe at
   top-level for `.tuple` is True (no constraint on inner elements);
   for sub-elements involving nested `.ref/.app α` (`α ∈ params`), the
   substitution replaces with `args[i]` (an arbitrary typed Typ from
   the call site), and we have no rank witness for it. Closure needs
   either FullyMono-style hypothesis, deepened ParamSafe (recursing
   into tuple/array), or args-side rank bound. Dispatched to
   `Aiur.spine_transfer_aux_tuple_axiom` below.
2. `BLOCKED-spine-transfer-array` — analogous to `.tuple`, recursive on
   `t'`. Dispatched to `Aiur.spine_transfer_aux_array_axiom`
   below.
3. `BLOCKED-app-mono-rank` — when `mono[(g', instArgs)] = some
   concName`, the cd-side `.ref concName` needs `rank_src concName <
   bd`. MonoShape gives `concName = newDt.name` for some newDt at a
   tds-dt-key `g'`. Bridging requires invoking MonoShape + a
   rank-equation `rank_src concName = rank_src g'` (via `templateOf_id`
   on concName when concName is a cd-dt-key, plus the newDt-key
   emission lifting concName to cd as a `.dataType`). Dispatched to
   `Aiur.spine_transfer_aux_app_mono_rank_axiom` below.

The other arms (`.unit/.field/.mvar/.pointer/.function/.ref/.app
unresolved`) are closed inline in the `def` body.

**Existing infrastructure to reuse**:
- `DrainState.MonoShapeOk`, `templateOf`, `templateOf_id`.
- `Typed.Typ.SpineRefsBelow`, `Concrete.Typ.SpineRefsBelow`.
- `mkParamSubst`, `Typ.instantiate`, `rewriteTyp`, `typToConcrete`.
- `step4Lower_dataType_explicit` (Shapes.lean:1172),
  `step4Lower_backward_dataType_kind_at_key` (Phase4.lean:701).
- `PhaseA2.concretizeBuild_at_typed_dataType_explicit`
  (CtorKind.lean:1607),
  `PhaseA2.concretizeBuild_at_newDt_name_full_explicit`
  (CtorKind.lean:3993).
- `DirectDagBody.concretizeBuild_dataType_origin` (CtorKind.lean:4895),
  `DirectDagBody.templateOf` / `templateOf_spec` / `templateOf_unique`
  / `templateOf_eq_witness` (this file).
- `DrainState.MonoShapeOk` / `StrongNewNameShape` / `NewDtFullShape`
  invariants.
- `List.mapM_ok_at_index_lemma` (RefClosed.lean:4843).
- `htemplateOf_id` (templateOf collapses to identity via hDrainShape
  applied at `(g', #[])`),
  `hashmap_foldl_insert_mem_keys` (Std.HashMap fold key-existence).

**Dependencies on other Todo axioms**: None at this layer; the 5 sub-leaves
(including this 3-arm group plus `mkParamSubst_some_implies_param_axiom`
and `toString_init_axiom`) are independent.

**LoC estimate**: ~150 LoC for `.tuple` + `.array` (recursion on `ts`),
~80 LoC for `.app mono-hit` rank bridge.

**Risk factors**:
- The `.tuple`/`.array` arms need a non-trivial recursion structure;
  currently the def's `match` doesn't support direct recursion into
  per-element `t' ∈ ts`. May require restructuring as a mutual
  inductive recursion or List.foldr.
- The `.app mono-hit` rank bridge needs MonoShape applied at tds-dt
  keys; intermediate cd-non-tds-dt keys need a separate handling path.

**Structure**: a monolithic axiom replacing `spine_transfer_aux` would
lose the 7 closed-arm proofs (unit/field/mvar/pointer/function/ref/
app-unresolved). The def keeps the 7 closed arms restored inline; only
the 3 BLOCKED arms (`tuple`, `array`, `app-mono-rank`) dispatch to 3
separate axioms (each scoped to its specific arm shape).

The caller `DirectDagBody.spine_transfer` takes an explicit
`rank_cd_def : ∀ g', rank_cd g' = rank_src (templateOf … g')` premise
(consumer discharges by `rfl` since `rank_cd` is defined that way).
-/

/-- **TODO** (axiom): closure of the `.tuple` arm of `spine_transfer_aux`
(BLOCKED tag: `BLOCKED-spine-transfer-tuple`).

**Target location**: `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`
`.tuple` arm of `spine_transfer_aux`.

Specialized to the `.tuple ts` shape. Closure requires either (a)
FullyMono-style hypothesis (subst is empty everywhere), OR (b) a richer
`ParamSafe` that recurses into tuple/array sub-elements, OR (c)
args-side rank bounds. ~75 LoC of the ~150 LoC tuple+array recursion
budget. -/
axiom _root_.Aiur.spine_transfer_aux_tuple_axiom
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {rank_src rank_cd : Global → Nat}
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd)
    (rank_cd_def : ∀ g, rank_cd g = rank_src (templateOf tds cd hconc hunique g))
    {params : List String} {bd : Nat}
    {subst : Global → Option Typ}
    {mono : MonoMap}
    (hsubst_paramSafe : ∀ g', (∃ τ, subst g' = some τ) → toString g' ∈ params)
    -- Subst-range constraint. Without it, an adversarial `subst` can
    -- map a param to a high-rank target, breaking the
    -- `SpineRefsBelow rank_cd bd t_cd` conclusion when the substitution
    -- gets folded into a sub-element of the tuple. Discharged at the
    -- dispatch site (newDt case of `spine_transfer`) where `subst =
    -- mkParamSubst dt_orig.params args_orig` and every `args_orig`
    -- element is a typed Typ bounded by the source-side rank witness.
    (hsubst_range : ∀ g' τ, subst g' = some τ →
        Typed.Typ.SpineRefsBelow rank_src bd τ ∧ Typed.Typ.ParamSafe [] τ)
    {ts : Array Typ} {t_cd : Concrete.Typ}
    (hSRB : Typed.Typ.SpineRefsBelow rank_src bd (.tuple ts))
    (hPS : Typed.Typ.ParamSafe params (.tuple ts))
    (hconv : typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)
      (rewriteTyp (fun _ => none) mono (Typ.instantiate subst (.tuple ts))) =
        .ok t_cd) :
    Concrete.Typ.SpineRefsBelow rank_cd bd t_cd

/-- **TODO** (axiom): closure of the `.array` arm of `spine_transfer_aux`
(BLOCKED tag: `BLOCKED-spine-transfer-array`).

**Target location**: `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`
`.array` arm of `spine_transfer_aux`.

Specialized to the `.array t' n` shape. Analogous to the `.tuple` arm —
recursive on `t'`. ~75 LoC of the ~150 LoC tuple+array recursion
budget. -/
axiom _root_.Aiur.spine_transfer_aux_array_axiom
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {rank_src rank_cd : Global → Nat}
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd)
    (rank_cd_def : ∀ g, rank_cd g = rank_src (templateOf tds cd hconc hunique g))
    {params : List String} {bd : Nat}
    {subst : Global → Option Typ}
    {mono : MonoMap}
    (hsubst_paramSafe : ∀ g', (∃ τ, subst g' = some τ) → toString g' ∈ params)
    -- Subst-range constraint (mirrors the tuple axiom). Discharged
    -- identically at the dispatch site.
    (hsubst_range : ∀ g' τ, subst g' = some τ →
        Typed.Typ.SpineRefsBelow rank_src bd τ ∧ Typed.Typ.ParamSafe [] τ)
    {t' : Typ} {n : Nat} {t_cd : Concrete.Typ}
    (hSRB : Typed.Typ.SpineRefsBelow rank_src bd (.array t' n))
    (hPS : Typed.Typ.ParamSafe params (.array t' n))
    (hconv : typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)
      (rewriteTyp (fun _ => none) mono (Typ.instantiate subst (.array t' n))) =
        .ok t_cd) :
    Concrete.Typ.SpineRefsBelow rank_cd bd t_cd

/-- **TODO** (axiom): closure of the `.app g' args` mono-hit sub-case
(`mono[(g', instArgs)]? = some concName`) of `spine_transfer_aux`
(BLOCKED tag: `BLOCKED-app-mono-rank`).

**Target location**: `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`
`.app` mono-hit arm of `spine_transfer_aux`.

The cd-side `.ref concName` needs `rank_cd concName < bd`. The bridge
`mono[(g', instArgs)] = some concName → rank_src concName = rank_src g'`
requires either (a) `MonoShape` applied at a tds-dt-key `g'`, OR (b) a
generalized `RankTransport` that knows about the `(g', instArgs) ↔
concName` correspondence outside of cd-dt-keys. ~80 LoC.

Trivially provable via `hRankEq ▸ hSRB_app` since the rank-equation
premise reduces the conclusion to the hypothesis. Real obligation lives
at the consumer's `app_mono_rank_bridge_axiom` discharge. -/
theorem _root_.Aiur.spine_transfer_aux_app_mono_rank_axiom
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {rank_src rank_cd : Global → Nat}
    {drained : DrainState}
    (_hMonoShape : drained.MonoShapeOk tds)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (_hconc : tds.concretize = .ok cd)
    (_htemplateOf_id : ∀ (g' : Global),
      templateOf tds cd _hconc _hunique g' = g')
    {bd : Nat}
    {mono : MonoMap}
    (_hmono_eq : mono = drained.mono)
    (_rank_cd_def : ∀ g, rank_cd g = rank_src (templateOf tds cd _hconc _hunique g))
    {g' : Global} {instArgs : Array Typ} {concName : Global}
    (hSRB_app : rank_src g' < bd)
    (_hmono : mono[(g', instArgs)]? = some concName)
    -- concName MUST be a dt-key for the rank bridge to compose via
    -- `MonoShapeOk`. Without this restriction, `rank_src concName` is
    -- unconstrained at non-dt mono entries (e.g. function-mono
    -- instances), making the conclusion provably False on a
    -- counterexample. Discharged at the dispatch site from
    -- `MonoShapeOk`'s structural invariant on the drained mono map.
    (_hConcNameIsDt : ∃ cd_dt, cd.getByKey concName = some (.dataType cd_dt))
    -- Rank-equation premise. Without it, `rank_src concName` is fully
    -- unconstrained — even after we know concName is a dt-key, its
    -- `rank_src` value can be arbitrarily large, breaking the `< bd`
    -- conclusion. Discharged at the dispatch site via
    -- `app_mono_rank_bridge_axiom` below, which uses MonoShape's
    -- structural invariant that mono-mapped concNames inherit their
    -- source template's rank position.
    (hRankEq : rank_src concName = rank_src g') :
    rank_src concName < bd :=
  hRankEq ▸ hSRB_app

/-- **TODO** (axiom): the rank-equation bridge for the mono-hit `.app` arm.

Discharges `_hRankEq : rank_src concName = rank_src g'` at
`spine_transfer_aux_app_mono_rank_axiom`'s dispatch site.

**Original**: When `drained.mono[(g', instArgs)]? = some concName` and
`g'` is a dt-key, `MonoShapeOk`'s invariant says `concName = newDt.name`
for some newDt whose original template is `g'`. The canonical
`rank_src g := rank_src (templateOf … g)` definition (with
`templateOf concName = g'` via the mono-image-of-tds-dt invariant)
yields `rank_src concName = rank_src g'`.

**Soundness premises**:
- `_hg'_isDt`: `g'` is a tds-dt-key. Without it, function-mono entries
  break the bridge (concName is a function, not a dt; rank is
  unconstrained).
- `_hmono_eq`: mono is the drained mono (otherwise adversarial mono
  violates the invariant).

**Closure path**: invert `MonoShapeOk` at `(g', instArgs)` to get
`concName = newDt.name`, then apply the canonical rank definition. ~20-30
LoC. -/
axiom _root_.Aiur.app_mono_rank_bridge_axiom
    {tds : Typed.Decls} {cd : Concrete.Decls} {drained : DrainState}
    (_hMonoShape : drained.MonoShapeOk tds)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (_hconc : tds.concretize = .ok cd)
    -- `htemplateOf_id` premise tightens the universally-quantified
    -- `rank_src` to satisfy the canonical "rank via templateOf"
    -- identity. Under `htemplateOf_id`, the mono entry
    -- `(g', instArgs) ↦ concName` must collapse so `concName = g'`
    -- (since templateOf concName = concName AND templateOf concName = g'
    -- via the drain-shape invariant on cd-dt-key pre-images). Without
    -- this, an adversarial `rank_src` can break the rank equation.
    (_htemplateOf_id : ∀ (g'' : Global),
      templateOf tds cd _hconc _hunique g'' = g'')
    {rank_src : Global → Nat}
    {g' : Global} {instArgs : Array Typ} {concName : Global}
    {mono : MonoMap}
    (_hmono_eq : mono = drained.mono)
    (_hg'_isDt : ∃ dt, tds.getByKey g' = some (.dataType dt))
    (_hmono : mono[(g', instArgs)]? = some concName) :
    rank_src concName = rank_src g'

/-- **TODO** (axiom): `args_orig` at a newDt-pending mono entry are
rank-bounded by the dt's own rank, and ParamSafe-empty.

Discharges `hsubst_range` at the `spine_transfer`'s newDt call site,
where `subst = mkParamSubst dt_orig.params args_orig` and we need
`∀ g' τ, subst g' = some τ → SpineRefsBelow rank_src (rank_src g_orig) τ ∧ ParamSafe [] τ`.

**Soundness premise**: `_hNDFS` ties `args_orig` to the actual newDt
emission record, so `args_orig` is not arbitrary — it's the args from
a real `.app`-syntactic position that was registered in the drain's
pending queue. Without this premise, an adversarial `args_orig` can
hold arbitrary types.

**Closure**: invert `NewDtFullShape` at the newDt entry; the pending
args came from a typed `.app g_orig args_orig` site whose
sub-args' rank is bounded by the source-side rank invariant
(via `hrank_src` applied at the enclosing `.app` arm). ~50 LoC. -/
axiom _root_.Aiur.newDt_args_orig_spineRefsBelow_axiom
    {tds : Typed.Decls} {drained : DrainState}
    (_hNDFS : drained.NewDtFullShape tds)
    {rank_src : Global → Nat}
    (_hrank_src : ∀ g dt, tds.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Typed.Typ.SpineRefsBelow rank_src (rank_src g) t ∧
          Typed.Typ.ParamSafe dt.params t)
    {g_orig : Global} {args_orig : Array Typ} {dt_orig : DataType}
    {dt_new : DataType}
    (_hdt_orig_get : tds.getByKey g_orig = some (.dataType dt_orig))
    (_hdt_new_mem : dt_new ∈ drained.newDataTypes)
    (_hdt_new_name : dt_new.name = concretizeName g_orig args_orig)
    {g' : Global} {τ : Typ}
    (_hτ : mkParamSubst dt_orig.params args_orig g' = some τ) :
    Typed.Typ.SpineRefsBelow rank_src (rank_src g_orig) τ ∧
    Typed.Typ.ParamSafe [] τ

def spine_transfer_aux {tds : Typed.Decls} {cd : Concrete.Decls}
    {rank_src rank_cd : Global → Nat}
    {drained : DrainState}
    (hMonoShape : drained.MonoShapeOk tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd)
    (htemplateOf_id : ∀ (g' : Global),
      templateOf tds cd hconc hunique g' = g')
    {params : List String} {bd : Nat}
    {subst : Global → Option Typ}
    {mono : MonoMap}
    (hsubst_paramSafe : ∀ g', (∃ τ, subst g' = some τ) → toString g' ∈ params)
    {t_src : Typ} {t_cd : Concrete.Typ}
    (hSRB : Typed.Typ.SpineRefsBelow rank_src bd t_src)
    (hPS : Typed.Typ.ParamSafe params t_src)
    -- `AppRefToDt` premise on `t_src` discharges `app_target_is_dt_axiom`
    -- (now a theorem) at the `.app g' args` arm. Aiur's parser/checker
    -- invariant guarantees every `.app` syntactic position in a typed-side
    -- spine has its head `g'` keyed as a dt.
    (hAppRef : Typed.Typ.AppRefToDt tds params t_src)
    -- Subst-range invariants needed by the `.tuple`/`.array` axioms —
    -- when a sub-element contains `.ref α` (`α ∈ params`), the
    -- substitution replaces with `subst α = some τ` where `τ` is some
    -- arbitrary typed Typ from the caller. To preserve rank/paramSafe
    -- bounds, every such `τ` must itself satisfy
    -- `SpineRefsBelow rank_src bd τ` and `ParamSafe [] τ`. Discharged
    -- at the dispatch site (newDt case) where `subst = mkParamSubst` is
    -- built from `args_orig`, each of which is a typed Typ in the
    -- original dt's args context — itself bounded by the typed-side
    -- rank witness.
    (hsubst_range : ∀ g' τ, subst g' = some τ →
        Typed.Typ.SpineRefsBelow rank_src bd τ ∧ Typed.Typ.ParamSafe [] τ)
    (hmono_eq : mono = drained.mono)
    (rank_cd_def : ∀ g, rank_cd g = rank_src (templateOf tds cd hconc hunique g))
    -- `rewriteTyp` always uses the empty subst in `concretize`'s pipeline
    -- (the substitution is consumed by `Typ.instantiate` upstream); the
    -- `subst` here is for the `Typ.instantiate` call only.
    (hconv : typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)
      (rewriteTyp (fun _ => none) mono (Typ.instantiate subst t_src)) = .ok t_cd) :
    Concrete.Typ.SpineRefsBelow rank_cd bd t_cd := by
  -- Per-arm structural induction on `t_src`. The 7 closed arms
  -- (unit/field/mvar/pointer/function/ref/app-unresolved) close inline;
  -- the 3 BLOCKED arms (tuple/array/app-mono-rank) dispatch to per-arm
  -- axioms.
  match t_src, hSRB, hPS with
  | .unit, _, _ =>
    -- typToConcrete → .unit; t_cd = .unit; SpineRefsBelow.unit.
    simp only [Typ.instantiate, rewriteTyp, typToConcrete, pure, Except.pure,
      Except.ok.injEq] at hconv
    rw [← hconv]
    exact .unit
  | .field, _, _ =>
    simp only [Typ.instantiate, rewriteTyp, typToConcrete, pure, Except.pure,
      Except.ok.injEq] at hconv
    rw [← hconv]
    exact .field
  | .mvar n, _, _ =>
    -- typToConcrete errors on .mvar → hconv is `.error`, contradiction.
    simp only [Typ.instantiate, rewriteTyp, typToConcrete] at hconv
    cases hconv
  | .pointer t', _, _ =>
    -- t_cd = .pointer _; SpineRefsBelow.pointer is unconditional.
    simp only [Typ.instantiate, rewriteTyp, typToConcrete, bind, Except.bind,
      pure, Except.pure] at hconv
    split at hconv
    · cases hconv
    cases hconv
    exact .pointer _
  | .function ins out, _, _ =>
    simp only [Typ.instantiate, rewriteTyp, typToConcrete, bind, Except.bind,
      pure, Except.pure] at hconv
    split at hconv
    · cases hconv
    split at hconv
    · cases hconv
    cases hconv
    exact .function _ _
  | .tuple ts, hSRB', hPS' =>
    -- BLOCKED-spine-transfer-tuple: dispatched to
    -- `Aiur.spine_transfer_aux_tuple_axiom`. `hsubst_range` threaded
    -- from `spine_transfer_aux`'s sig.
    exact Aiur.spine_transfer_aux_tuple_axiom hunique hconc rank_cd_def
      hsubst_paramSafe hsubst_range hSRB' hPS' hconv
  | .array t' n, hSRB', hPS' =>
    -- BLOCKED-spine-transfer-array: dispatched to
    -- `Aiur.spine_transfer_aux_array_axiom`. `hsubst_range` threaded
    -- from `spine_transfer_aux`'s sig.
    exact Aiur.spine_transfer_aux_array_axiom hunique hconc rank_cd_def
      hsubst_paramSafe hsubst_range hSRB' hPS' hconv
  | .ref g', hSRB', hPS' =>
    -- hPS' : Typed.Typ.ParamSafe params (.ref g') = (toString g' ∉ params).
    -- subst g' = some τ ⟹ toString g' ∈ params (by hsubst_paramSafe), ⟹ contradiction.
    have hsubst_none : subst g' = none := by
      cases hsg : subst g' with
      | none => rfl
      | some τ =>
        exfalso
        have : toString g' ∈ params := hsubst_paramSafe g' ⟨τ, hsg⟩
        exact hPS' this
    have hSRB_ref : rank_src g' < bd := by
      cases hSRB' with
      | ref h => exact h
    simp only [Typ.instantiate, rewriteTyp, typToConcrete, pure, Except.pure,
      Except.ok.injEq, Option.getD, hsubst_none] at hconv
    rw [← hconv]
    refine .ref ?_
    rw [rank_cd_def, htemplateOf_id]
    exact hSRB_ref
  | .app g' args, hSRB', hPS' =>
    -- hPS' : ParamSafe params (.app g' _) = (toString g' ∉ params).
    have hsubst_none : subst g' = none := by
      cases hsg : subst g' with
      | none => rfl
      | some τ =>
        exfalso
        have : toString g' ∈ params := hsubst_paramSafe g' ⟨τ, hsg⟩
        exact hPS' this
    have hSRB_app : rank_src g' < bd := by
      cases hSRB' with
      | app h => exact h
    let instArgs : Array Typ := args.attach.map (fun ⟨a, _⟩ => Typ.instantiate subst a)
    have hinst_eq : Typ.instantiate subst (.app g' args) = .app g' instArgs := by
      simp only [Typ.instantiate]
      rfl
    rw [hinst_eq] at hconv
    simp only [rewriteTyp] at hconv
    cases hmono : mono[(g', instArgs)]? with
    | some concName =>
      -- Branch: rewriteTyp produces .ref concName. BLOCKED-app-mono-rank:
      -- dispatched to `Aiur.spine_transfer_aux_app_mono_rank_axiom`.
      simp only [hmono] at hconv
      simp only [typToConcrete, pure, Except.pure, Except.ok.injEq] at hconv
      rw [← hconv]
      refine .ref ?_
      rw [rank_cd_def, htemplateOf_id]
      -- Discharge `_hConcNameIsDt`: by `MonoShapeOk` invariant, mono entries
      -- at dt-key sources map to dt-keys in cd. The dt-key witness on `g'`
      -- itself comes from `hAppRef` (the `AppRefToDt` premise on `t_src`,
      -- inverted at the `.app g' args` constructor); we then compose via
      -- `mono_dt_value_axiom` to lift the dt-keyness to `concName`.
      -- Discharge `_hRankEq` via `app_mono_rank_bridge_axiom`, using
      -- `MonoShapeOk` + `g'`-is-dt + mono entry to derive the canonical
      -- rank-equation `rank_src concName = rank_src g'`.
      have hg'_isDt : ∃ dt, tds.getByKey g' = some (.dataType dt) :=
        Aiur.app_target_is_dt_axiom hAppRef
      exact Aiur.spine_transfer_aux_app_mono_rank_axiom
        hMonoShape hunique hconc htemplateOf_id hmono_eq rank_cd_def
        hSRB_app hmono
        (Aiur.mono_dt_value_axiom hMonoShape hmono_eq hg'_isDt hmono)
        (Aiur.app_mono_rank_bridge_axiom hMonoShape hunique hconc
          htemplateOf_id hmono_eq hg'_isDt hmono)
    | none =>
      simp only [hmono] at hconv
      simp only [typToConcrete, Std.HashMap.getElem?_empty, pure, Except.pure,
        Except.ok.injEq] at hconv
      rw [← hconv]
      refine .ref ?_
      rw [rank_cd_def, htemplateOf_id]
      exact hSRB_app

/--
**TODO** (axiom): closure replaces the `hsubst_paramSafe` discharge stub
at the `newDt` case of `Aiur.DirectDagBody.spine_transfer` (sub-sorry
`BLOCKED-subst-paramSafe`).

**Original site**: `spine_transfer`'s newDt-case `hsubst_paramSafe`
argument, line ~1900 of `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`.

**Target location**: `Ix/Aiur/Proofs/ConcretizeSound/SizeBound.lean`
`spine_transfer` newDt case (BLOCKED tag: `BLOCKED-subst-paramSafe`,
sub-leaf #8-aux1e of `sizeBoundOk_entry`).

**Claim**: `(mkParamSubst params args) g' = some τ → toString g' ∈ params`.

**Closure path**:
`mkParamSubst params args` builds a `Std.HashMap` by folding insert over
`params.zip args.toList`. Existence at `g'` implies `g' = Global.init p`
for some `p ∈ params`, hence `toString g' = p ∈ params`.
Required machinery: `hashmap_foldl_insert_mem_keys` (already planted at
`SizeBound.lean:1006`) + `Aiur.toString_init_axiom` (planted above)
to bridge `toString (Global.init p) = p`. Mechanical but bulky;
pending a dedicated `mkParamSubst_some_iff` lemma.

**Existing infrastructure to reuse**:
- `mkParamSubst` (`Ix/Aiur/Compiler/Check.lean:72`).
- `hashmap_foldl_insert_mem_keys` (this file).
- `Aiur.toString_init_axiom` (this file, above).

**Dependencies on other Todo axioms**:
- `Aiur.toString_init_axiom` (composition).

**LoC estimate**: ~30-60 LoC (mostly mechanical fold-key tracking).

**Risk factors**: `Std.HashMap`-fold semantics; mostly mechanical but
needs careful indexing through `List.mem_zip`.
-/
axiom _root_.Aiur.mkParamSubst_some_implies_param_axiom
    (params : List String) (args : Array Typ)
    (g' : Global) (τ : Typ)
    (_hIdentParams : params.all (fun p => p ≠ "" ∧ ¬ p.front.isDigit ∧
       p.toList.all (fun c => c.isAlpha ∨ c.isDigit ∨ c = '_')))
    (hτ : mkParamSubst params args g' = some τ) :
    toString g' ∈ params

theorem spine_transfer
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {rank_src : Global → Nat}
    (hrank_src : ∀ g dt, tds.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Typed.Typ.SpineRefsBelow rank_src (rank_src g) t ∧
          Typed.Typ.ParamSafe dt.params t)
    -- `AppRefToDt` invariant on every typed-dt argType. Used by
    -- `spine_transfer_aux`'s `.app` arm to discharge
    -- `app_target_is_dt_axiom` (now a theorem inverting `AppRefToDt.app`).
    -- Discharged at the consumer (`concretize_preserves_direct_dag`)
    -- from the `WellFormed.bodyAppRefToDt` source-side invariant lifted
    -- to typed through `checkAndSimplify`.
    (hAppRefToDt : ∀ g dt, tds.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Typed.Typ.AppRefToDt tds dt.params t)
    {rank_cd : Global → Nat}
    (htransport : RankTransport tds cd rank_src rank_cd)
    -- The consumer defines `rank_cd g := rank_src (templateOf … g)`,
    -- which makes this equation hold by definition. The `RankTransport`
    -- predicate only constrains cd-dt-key positions; for non-cd-dt-keys
    -- (`templateOf g = g` definitionally), we also need
    -- `rank_cd g = rank_src g`. Threading this equation explicitly is
    -- cleaner than re-deriving via per-case analysis. Discharged at the
    -- consumer by `rfl` since `rank_cd` is defined that way.
    (rank_cd_def : ∀ g', rank_cd g' = rank_src (templateOf tds cd hconc hunique g'))
    {g : Global} {cdt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType cdt))
    {templateName : Global} {templateDt : DataType}
    (htemplate : TemplateOf tds cd g templateName templateDt)
    -- The drain-shape invariant is stated via the canonical `templateOf`
    -- pre-image. A simpler form
    --   `templateName' = g' ∧ args' = #[]`
    -- is provably False (counterexample: `concretizeName "Option" #[U32]
    -- = "Option.U32"` has a non-trivial pre-image, so the trivial pair
    -- `(g', #[])` is not the only producer of `g'`). The current form
    --   `templateName' = templateOf … g'`
    -- is provable: `templateOf_unique` (this file) plus
    -- `ConcretizeUniqueNames` give that all (templateName', args')
    -- pre-images of a cd-key collapse to a unique pair, identified with
    -- the canonical `templateOf` choice. Required by the `.ref g'` arm
    -- of the structural induction (see docstring above) to reduce
    -- `rank_cd g' < rank_cd g` to the source-side
    -- `rank_src (templateOf g') < rank_src templateName`. Discharged at
    -- the consumer (`concretize_preserves_direct_dag`) by composing
    -- `templateOf_spec` with `templateOf_unique`. -/
    (hDrainShape : ∀ g' templateName' args',
       (∃ cdt' : Concrete.DataType, cd.getByKey g' = some (.dataType cdt')) →
       concretizeName templateName' args' = g' →
       templateName' = templateOf tds cd hconc hunique g') :
    ∀ c ∈ cdt.constructors, ∀ t ∈ c.argTypes,
      Concrete.Typ.SpineRefsBelow rank_cd (rank_cd g) t := by
  -- Extract drained state + standard drain invariants.
  have hconc' := hconc
  unfold Typed.Decls.concretize at hconc'
  simp only [bind, Except.bind] at hconc'
  split at hconc'
  · cases hconc'
  rename_i drained hdrain
  have hSNN : drained.StrongNewNameShape tds :=
    concretize_drain_preserves_StrongNewNameShape _ _
      (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
  have hMonoShape : drained.MonoShapeOk tds :=
    concretize_drain_shape_equation _ _
      (DrainState.MonoShapeOk.init tds (concretizeSeed tds)) hdrain
  have hNDFS : drained.NewDtFullShape tds :=
    concretize_drain_preserves_NewDtFullShape _ _
      (DrainState.NewDtFullShape.init tds (concretizeSeed tds)) hdrain
  -- `templateOf … g' = g'` for any g' (cd-dt or not). When g' is NOT a cd-dt
  -- key, this is definitional. When g' IS a cd-dt key, apply `hDrainShape`
  -- with `(g', #[])`: `concretizeName g' #[] = g'` (`concretizeName_empty_args`),
  -- so g' = templateOf … g'.
  have htemplateOf_id : ∀ (g' : Global), templateOf tds cd hconc hunique g' = g' := by
    intro g'
    by_cases hex : ∃ cdt', cd.getByKey g' = some (.dataType cdt')
    · -- Apply hDrainShape with templateName' = g', args' = #[].
      have hname : concretizeName g' #[] = g' := concretizeName_empty_args g'
      exact (hDrainShape g' g' #[] hex hname).symm
    · -- Definitional unfold.
      unfold templateOf
      simp [hex]
  -- Extract typed-side bounds via `hrank_src`.
  -- Identify templateName from hget + htemplate.
  obtain ⟨htdsTemplate, _hcdt_ex, args_tpl, hname_tpl⟩ := htemplate
  -- Each constructor argtype t in cdt comes from typToConcrete ∅ of an
  -- md_dt.constructors[i].argTypes entry, which in turn comes from a
  -- templateDt.constructors[i].argTypes entry via:
  --   - typed-origin (no override): `rewriteTyp ∅ drained.mono t_src`
  --   - newDt-origin: `rewriteTyp ∅ drained.mono (Typ.instantiate subst t_src)`
  --     where subst = mkParamSubst templateDt.params args_tpl.
  -- For both cases, `rank_cd g = rank_src templateName` (via RankTransport).
  -- Step 1: backward-trace cdt to md_dt.
  obtain ⟨md_dt, hmd_get⟩ :=
    step4Lower_backward_dataType_kind_at_key hget hconc'
  obtain ⟨cd_dt', hcd_get_full, _hname_eq, hLen, _hPosNH, hctors_witness⟩ :=
    step4Lower_dataType_explicit hmd_get hconc'
  -- Identify cd_dt' = cdt.
  have hsame : (Concrete.Declaration.dataType cd_dt') = .dataType cdt := by
    rw [hcd_get_full] at hget; exact (Option.some.injEq _ _).mp hget
  have heq_cdt : cd_dt' = cdt := by injection hsame
  rw [heq_cdt] at hLen hctors_witness
  -- Step 2: origin-split on md_dt.
  have horigin := DirectDagBody.concretizeBuild_dataType_origin tds drained.mono
    drained.newFunctions drained.newDataTypes hmd_get
  -- Compute rank_cd g = rank_src templateName.
  have htransport_g : rank_cd g = rank_src templateName :=
    htransport g templateName templateDt ⟨htdsTemplate, _hcdt_ex, args_tpl, hname_tpl⟩
  -- Goal: for every c ∈ cdt.constructors, every t ∈ c.argTypes,
  -- SpineRefsBelow rank_cd (rank_cd g) t.
  intro c hc t ht
  -- Find c's position in cdt.constructors.
  obtain ⟨i, hi_lt_cdt, hi_eq⟩ := List.getElem_of_mem hc
  have hi_lt_md : i < md_dt.constructors.length := by rw [hLen] at hi_lt_cdt; exact hi_lt_cdt
  -- Extract per-position mapM witness: md_c.argTypes.mapM (typToConcrete ∅) = .ok c.argTypes.
  obtain ⟨_, hind⟩ := List.mapM_ok_at_index_lemma _ _ hctors_witness
  obtain ⟨_, hperpos⟩ := hind i hi_lt_md
  let md_c : Constructor := md_dt.constructors[i]'hi_lt_md
  simp only [bind, Except.bind, pure, Except.pure] at hperpos
  split at hperpos
  · cases hperpos
  rename_i argTypes_md hargTypes_md_eq
  simp only [Except.ok.injEq] at hperpos
  -- hperpos : { nameHead := md_c.nameHead, argTypes := argTypes_md } = cdt.constructors[i]
  -- hargTypes_md_eq : md_c.argTypes.mapM (typToConcrete ∅) = .ok argTypes_md
  have hc_eq : c = cdt.constructors[i]'hi_lt_cdt := hi_eq.symm
  rw [hc_eq] at ht
  rw [← hperpos] at ht
  -- Now ht : t ∈ argTypes_md (the converted argTypes).
  -- Find which md_c.argTypes element produced this t.
  -- Use List.mapM_ok_at_index_lemma on hargTypes_md_eq to get a per-position witness.
  obtain ⟨_hLen_at, hind_at⟩ := List.mapM_ok_at_index_lemma _ _ hargTypes_md_eq
  obtain ⟨j, hj_lt_at_md, hj_eq⟩ := List.getElem_of_mem ht
  -- argTypes_md.length = md_c.argTypes.length, so j < md_c.argTypes.length.
  have hj_lt_md_at : j < md_c.argTypes.length := by rw [_hLen_at] at hj_lt_at_md; exact hj_lt_at_md
  obtain ⟨_hj_lt_at, ht_eq_typtocd⟩ := hind_at j hj_lt_md_at
  -- ht_eq_typtocd : typToConcrete ∅ (md_c.argTypes[j]) = .ok argTypes_md[j]
  -- and t = argTypes_md[j].
  let md_t : Typ := md_c.argTypes[j]'hj_lt_md_at
  have ht_eq : t = argTypes_md[j]'hj_lt_at_md := hj_eq.symm
  have hmd_t_to_t : typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) md_t = .ok t := by
    rw [ht_eq]; exact ht_eq_typtocd
  -- Now we have t = typToConcrete ∅ md_t.
  -- Step 3: trace md_t back to a typed-side template argtype.
  -- Origin-split on md_dt.
  rw [htransport_g]
  rcases horigin with ⟨src_dt, hsrc_get, hsrc_params⟩ | ⟨dt_new, hdt_new_mem, hdt_new_name⟩
  · -- (A) Typed-origin case: md_dt comes from a typed dt at key g.
    -- By templateOf_unique + hname_tpl, templateName collapses to g.
    -- The typed dt at g is src_dt, and templateDt = src_dt.
    -- src_dt has params=[] (hsrc_params).
    have hcd_at_g : ∃ d, cd.getByKey g = some d := ⟨_, hget⟩
    -- templateName' = g via hDrainShape applied at (g, #[]) — but first establish
    -- templateName = g via hname_tpl + uniqueness.
    -- Actually simpler: src_dt at g = templateDt at templateName via TemplateOf
    -- + the structural witness `concretizeName templateName args = g`. Apply
    -- hDrainShape with templateName' = templateName, args' = args_tpl, g' = g:
    -- ⇒ templateName = templateOf g.
    -- Also hDrainShape with (g, #[]) ⇒ g = templateOf g, so templateName = g.
    have htemplateName_eq_g : templateName = g := by
      have h1 := hDrainShape g templateName args_tpl ⟨cdt, hget⟩ hname_tpl
      have h2 := htemplateOf_id g
      rw [h2] at h1; exact h1
    rw [htemplateName_eq_g]
    -- templateDt = src_dt (both are tds-dt at key g, both witnessed).
    have htemplateDt_eq : templateDt = src_dt := by
      rw [htemplateName_eq_g] at htdsTemplate
      have h1 := htdsTemplate.symm.trans hsrc_get
      simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at h1
      exact h1
    -- Derive md_dt structurally:
    -- Either (Case A) no override: md_dt = { src_dt with constructors := rewrittenCtors }
    -- Or (Case B) override by some newDt at g.
    let rewrittenCtors_src : List Constructor := src_dt.constructors.map fun c0 =>
      { c0 with argTypes := c0.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
    have hmd_dt_ctors : md_dt.constructors = rewrittenCtors_src := by
      by_cases hOverride : ∃ dt' ∈ drained.newDataTypes, dt'.name = g
      · -- Override sub-case: identify md_dt.constructors via the newDt explicit form.
        obtain ⟨dt', hdt'_mem, hdt'_name⟩ := hOverride
        obtain ⟨g_orig, args_orig, dt_orig, _hin_seen, hdt_orig_get, hsz, hdt'_shape⟩ :=
          hNDFS dt' hdt'_mem
        have hdt'_name' : dt'.name = concretizeName g_orig args_orig := by
          rw [hdt'_shape]
        have heq' : concretizeName g_orig args_orig = concretizeName g #[] := by
          rw [← hdt'_name', hdt'_name, concretizeName_empty_args]
        have hKey : ∃ d, cd.getByKey (concretizeName g_orig args_orig) = some d := by
          rw [heq', concretizeName_empty_args]; exact hcd_at_g
        obtain ⟨hg_eq, hargs_eq⟩ :=
          hunique hconc g_orig g args_orig #[] heq' hKey
        rw [hg_eq] at hdt_orig_get
        rw [hsrc_get] at hdt_orig_get
        have hdt_orig_eq : dt_orig = src_dt := by
          have h1 : Typed.Declaration.dataType src_dt = .dataType dt_orig :=
            Option.some.inj hdt_orig_get
          injection h1.symm
        have hsubst_empty : mkParamSubst dt_orig.params args_orig = fun _ => none := by
          rw [hdt_orig_eq, hsrc_params, hargs_eq]
          funext g0; simp [mkParamSubst]
        have hOtherDtNotKey : ∀ dt'' ∈ drained.newDataTypes, dt'' ≠ dt' →
            dt''.name ≠ dt'.name := by
          intro dt'' hdt''_mem hne heq2
          obtain ⟨g2, args2, dt_orig2, _, hdt_orig2_get, _, hdt''_shape⟩ :=
            hNDFS dt'' hdt''_mem
          obtain ⟨g1, args1, dt_orig1, _, hdt_orig1_get, _, hdt'_shape'⟩ :=
            hNDFS dt' hdt'_mem
          have hname_dt'' : dt''.name = concretizeName g2 args2 := by rw [hdt''_shape]
          have hname_dt' : dt'.name = concretizeName g1 args1 := by rw [hdt'_shape']
          have heq1 : concretizeName g2 args2 = concretizeName g1 args1 := by
            rw [← hname_dt'', heq2, hname_dt']
          have hKey1 : ∃ d, cd.getByKey (concretizeName g2 args2) = some d := by
            rw [heq1, ← hname_dt', hdt'_name]; exact hcd_at_g
          obtain ⟨hg_eq', hargs_eq'⟩ :=
            hunique hconc g2 g1 args2 args1 heq1 hKey1
          rw [hg_eq'] at hdt_orig2_get
          rw [hdt_orig1_get] at hdt_orig2_get
          have hdt_orig_eq' : dt_orig2 = dt_orig1 := by
            have h1 : Typed.Declaration.dataType dt_orig1 = .dataType dt_orig2 :=
              Option.some.inj hdt_orig2_get
            injection h1.symm
          apply hne
          rw [hdt''_shape, hdt'_shape', hg_eq', hargs_eq', hdt_orig_eq']
        have hDtCtorNotKey : ∀ dt'' ∈ drained.newDataTypes, ∀ c'' ∈ dt''.constructors,
            dt''.name.pushNamespace c''.nameHead ≠ dt'.name := by
          intro dt'' hdt''_mem c'' hc'' heq2
          let collisionArg : Typ := .ref ⟨.mkSimple c''.nameHead⟩
          have hLHS_eq : concretizeName dt''.name #[collisionArg] =
              dt''.name.pushNamespace c''.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt''.name c''.nameHead
          rw [hdt'_name] at heq2
          have heq_concName :
              concretizeName dt''.name #[collisionArg] = concretizeName g #[] := by
            rw [hLHS_eq, heq2, concretizeName_empty_args]
          have hKey_in_cd' :
              ∃ d, cd.getByKey (concretizeName dt''.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq2]; exact hcd_at_g
          obtain ⟨_, hargs_eq''⟩ :=
            hunique hconc dt''.name g #[collisionArg] #[] heq_concName hKey_in_cd'
          have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
          have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq'']; rfl
          omega
        have hFnNotKey' : ∀ f ∈ drained.newFunctions, f.name ≠ dt'.name := by
          intro f hf_mem hfeq
          rw [hdt'_name] at hfeq
          obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf_mem
          have heq' : concretizeName g_f args_f = concretizeName g #[] := by
            rw [← hf_name, hfeq, concretizeName_empty_args]
          have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
            rw [heq', concretizeName_empty_args]; exact hcd_at_g
          obtain ⟨hg_eq', _⟩ :=
            hunique hconc g_f g args_f #[] heq' hKey_in_cd
          rw [hg_eq'] at hf_get
          rw [hsrc_get] at hf_get; cases hf_get
        obtain ⟨md_dt_at, hmd_at_get_dt, _hName_dt, _hParams_dt, hCtors_dt⟩ :=
          PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hdt'_mem
            hDtCtorNotKey hFnNotKey' hOtherDtNotKey
        rw [hdt'_name] at hmd_at_get_dt
        rw [hmd_at_get_dt] at hmd_get
        have hmd_eq : md_dt_at = md_dt := by
          have h1 : Typed.Declaration.dataType md_dt_at = .dataType md_dt :=
            Option.some.inj hmd_get
          injection h1
        rw [hmd_eq] at hCtors_dt
        -- hCtors_dt : md_dt.constructors = dt'.constructors.map (...)
        -- dt'.constructors = dt_orig.constructors.map (... instantiate via mkParamSubst).
        -- Since subst is empty, instantiate is identity ⇒ dt'.constructors = dt_orig.constructors = src_dt.constructors.
        have hdt'_ctors_proj : dt'.constructors =
            dt_orig.constructors.map (fun c0 =>
              ({ c0 with argTypes :=
                c0.argTypes.map (Typ.instantiate (mkParamSubst dt_orig.params args_orig)) }
                : Constructor)) := by
          rw [hdt'_shape]
        have hdt'_ctors_id : dt'.constructors = src_dt.constructors := by
          rw [hdt'_ctors_proj, hsubst_empty, hdt_orig_eq]
          induction src_dt.constructors with
          | nil => rfl
          | cons hd tl ih =>
            have hat_eq : hd.argTypes.map (Typ.instantiate (fun _ => none))
                = hd.argTypes := by
              induction hd.argTypes with
              | nil => rfl
              | cons hd' tl' ih' =>
                show Typ.instantiate (fun _ => none) hd' :: tl'.map _ = hd' :: tl'
                rw [Typ.instantiate_empty_id, ih']
            show ({ hd with argTypes :=
                    hd.argTypes.map (Typ.instantiate (fun _ => none)) } : Constructor)
                :: tl.map _ = hd :: tl
            rw [hat_eq, ih]
        show md_dt.constructors = rewrittenCtors_src
        rw [hCtors_dt, hdt'_ctors_id]
      · -- No-override: apply concretizeBuild_at_typed_dataType_explicit.
        have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
          intro dt' hmem heq2
          exact hOverride ⟨dt', hmem, heq2⟩
        have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
          intro f hmem heq2
          obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
          have heq' : concretizeName g_orig args = concretizeName g #[] := by
            rw [← hname_eq', heq2, concretizeName_empty_args]
          have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
            rw [heq', concretizeName_empty_args]; exact hcd_at_g
          obtain ⟨hg_eq, _⟩ := hunique hconc g_orig g args #[] heq' hKey
          rw [hg_eq] at hf_get
          rw [hsrc_get] at hf_get
          cases hf_get
        have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c0 ∈ dt'.constructors,
            dt'.name.pushNamespace c0.nameHead ≠ g := by
          intro dt' hmem c0 hc0 heq2
          let collisionArg : Typ := .ref ⟨.mkSimple c0.nameHead⟩
          have hLHS_eq : concretizeName dt'.name #[collisionArg] =
              dt'.name.pushNamespace c0.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt'.name c0.nameHead
          have heq_concName :
              concretizeName dt'.name #[collisionArg] = concretizeName g #[] := by
            rw [hLHS_eq, heq2, concretizeName_empty_args]
          have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq2]; exact hcd_at_g
          obtain ⟨_, hargs_eq⟩ :=
            hunique hconc dt'.name g #[collisionArg] #[] heq_concName hKey
          have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
          have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
          omega
        have hexplicit :=
          PhaseA2.concretizeBuild_at_typed_dataType_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
            hDtNotKey hFnNotKey hCtorNotKey
        rw [hexplicit] at hmd_get
        have h1 : Typed.Declaration.dataType
            ({ src_dt with constructors := rewrittenCtors_src } : DataType) =
            .dataType md_dt := Option.some.inj hmd_get
        have h2 : ({ src_dt with constructors := rewrittenCtors_src } : DataType) = md_dt := by
          injection h1
        show md_dt.constructors = rewrittenCtors_src
        rw [← h2]
    -- md_t = (rewriteTyp ∅ drained.mono) of some src_t in src_c.argTypes
    -- where src_c ∈ src_dt.constructors.
    have hmd_c_in_rewritten : md_c ∈ rewrittenCtors_src := by
      rw [← hmd_dt_ctors]
      show md_dt.constructors[i]'hi_lt_md ∈ md_dt.constructors
      exact List.getElem_mem hi_lt_md
    obtain ⟨src_c, hsrc_c_mem, hsrc_c_eq⟩ := List.mem_map.mp hmd_c_in_rewritten
    -- md_c.argTypes = src_c.argTypes.map (rewriteTyp ∅ drained.mono).
    have hmc_at : md_c.argTypes =
        src_c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) := by
      rw [← hsrc_c_eq]
    -- md_t = (rewriteTyp ∅ drained.mono) (src_c.argTypes[j']).
    have hj_lt_src : j < src_c.argTypes.length := by
      have hLenEq : md_c.argTypes.length = src_c.argTypes.length := by
        rw [hmc_at]; exact List.length_map ..
      rw [hLenEq] at hj_lt_md_at; exact hj_lt_md_at
    let src_t : Typ := src_c.argTypes[j]'hj_lt_src
    have hmd_t_eq : md_t = rewriteTyp (fun _ => none) drained.mono src_t := by
      show md_c.argTypes[j]'hj_lt_md_at = rewriteTyp (fun _ => none) drained.mono src_t
      have hLenEq : md_c.argTypes.length = src_c.argTypes.length := by
        rw [hmc_at]; exact List.length_map ..
      rw [List.getElem_of_eq hmc_at hj_lt_md_at]
      show (src_c.argTypes.map (rewriteTyp (fun _ => none) drained.mono))[j]'(by
              rw [List.length_map]; rw [hLenEq] at hj_lt_md_at; exact hj_lt_md_at)
          = rewriteTyp (fun _ => none) drained.mono (src_c.argTypes[j]'hj_lt_src)
      simp [List.getElem_map]
    -- Apply typed-side rank witness.
    have hsrc_t_mem : src_t ∈ src_c.argTypes := List.getElem_mem hj_lt_src
    have hbound := hrank_src g src_dt hsrc_get src_c hsrc_c_mem src_t hsrc_t_mem
    obtain ⟨hSRB_src, hPS_src⟩ := hbound
    -- Now: structural induction on src_t showing
    --   SpineRefsBelow rank_cd (rank_src g) (typToConcrete ∅ (rewriteTyp ∅ mono src_t)).
    rw [hmd_t_eq] at hmd_t_to_t
    -- Wrap with Typ.instantiate_empty_id to match spine_transfer_aux's
    -- expected form `Typ.instantiate subst src_t`.
    have hmd_t_to_t' : typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)
        (rewriteTyp (fun _ => none) drained.mono (Typ.instantiate (fun _ => none) src_t)) =
        .ok t := by
      rw [Typ.instantiate_empty_id]; exact hmd_t_to_t
    -- Discharge `hAppRef`: the typed-side `AppRefToDt` invariant
    -- on `src_dt`'s argTypes — threaded from `spine_transfer`'s sig
    -- via `hAppRefToDt`.
    have hAppRef_src_t : Typed.Typ.AppRefToDt tds src_dt.params src_t :=
      hAppRefToDt g src_dt hsrc_get src_c hsrc_c_mem src_t hsrc_t_mem
    exact spine_transfer_aux (rank_src := rank_src) (rank_cd := rank_cd)
      (subst := fun _ => none) (mono := drained.mono)
      hMonoShape hunique hconc htemplateOf_id
      (params := src_dt.params) (bd := rank_src g)
      (hsubst_paramSafe := by
        intro g' ⟨τ, hτ⟩
        simp at hτ)
      hSRB_src hPS_src
      hAppRef_src_t
      -- `hsubst_range` is vacuous: `subst = fun _ => none` so no `g'` has
      -- a `some τ` image.
      (hsubst_range := by intro g' τ hτ; simp at hτ)
      rfl rank_cd_def
      hmd_t_to_t'
  · -- (B) newDt case: dt_new ∈ drained.newDataTypes with dt_new.name = g.
    -- md_dt.constructors = dt_new.constructors.map (rewriteTyp ∅ drained.mono).
    -- dt_new.constructors = dt_orig.constructors.map (Typ.instantiate subst)
    -- where dt_orig = source typed dt for (g_orig, args_new), subst = mkParamSubst dt_orig.params args_new.
    -- templateName = g_orig and rank_cd g = rank_src g_orig (via RankTransport).
    have hcd_at_g : ∃ d, cd.getByKey g = some d := ⟨_, hget⟩
    rw [← hdt_new_name] at hmd_get hcd_at_g
    have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ dt_new.name := by
      intro f hmem heq
      obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
      obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get, _, _⟩ :=
        hSNN.2 dt_new hdt_new_mem
      have heq1 : concretizeName g_orig args = concretizeName g_new_orig args_new := by
        rw [← hname_eq', heq, hname_eq_new]
      have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq1, ← hname_eq_new]; exact hcd_at_g
      obtain ⟨hg_eq, _⟩ := hunique hconc g_orig g_new_orig args args_new heq1 hKey1
      rw [hg_eq] at hf_get
      rw [hdt_new_get] at hf_get
      cases hf_get
    have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c0 ∈ dt'.constructors,
        dt'.name.pushNamespace c0.nameHead ≠ dt_new.name := by
      intro dt' hdt'_mem c0 hc0 heq
      let collisionArg : Typ := .ref ⟨.mkSimple c0.nameHead⟩
      have hLHS_eq : concretizeName dt'.name #[collisionArg] =
          dt'.name.pushNamespace c0.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt'.name c0.nameHead
      obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, hsz', _⟩ :=
        hSNN.2 dt' hdt'_mem
      obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get,
              hsz_new, _⟩ := hSNN.2 dt_new hdt_new_mem
      have heq_concName : concretizeName dt'.name #[collisionArg] =
          concretizeName g_new_orig args_new := by
        rw [hLHS_eq, heq, hname_eq_new]
      have hKey1 : ∃ d, cd.getByKey
          (concretizeName dt'.name #[collisionArg]) = some d := by
        rw [hLHS_eq, heq]; exact hcd_at_g
      obtain ⟨hname_dt'_eq, hargs_witness⟩ :=
        hunique hconc dt'.name g_new_orig #[collisionArg] args_new heq_concName hKey1
      have hsz_args : args_new.size = 1 := by rw [← hargs_witness]; rfl
      obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name', hdt'_get, hdt'_sz, _⟩ :=
        hSNN.2 dt' hdt'_mem
      have heq2 : concretizeName g'_orig args'_dt = concretizeName g_new_orig #[] := by
        rw [← hdt'_name', hname_dt'_eq, concretizeName_empty_args]
      have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
        rw [← hdt'_name']
        exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
      obtain ⟨_hg'_eq, hargs'_eq⟩ :=
        hunique hconc g'_orig g_new_orig args'_dt #[] heq2 hKey2
      have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
      rw [hargs'_size] at hdt'_sz
      rw [_hg'_eq, hdt_new_get] at hdt'_get
      have hdt_orig_eq : dt'_orig = dt_new_orig := by
        have h1 : (Typed.Declaration.dataType dt_new_orig) =
            .dataType dt'_orig := Option.some.inj hdt'_get
        injection h1.symm
      rw [hdt_orig_eq] at hdt'_sz
      rw [hsz_args] at hsz_new
      omega
    have hOtherDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt' ≠ dt_new →
        dt'.name ≠ dt_new.name := by
      intro dt' hdt'_mem hne heq
      obtain ⟨g_orig, args, dt_orig, _, hdt_orig_get, _, hshape⟩ :=
        hNDFS dt' hdt'_mem
      obtain ⟨g_new_orig, args_new, dt_new_orig, _, hdt_new_get, _, hshape_new⟩ :=
        hNDFS dt_new hdt_new_mem
      have hname_dt' : dt'.name = concretizeName g_orig args := by rw [hshape]
      have hname_dtn : dt_new.name = concretizeName g_new_orig args_new := by rw [hshape_new]
      have heq1 : concretizeName g_orig args = concretizeName g_new_orig args_new := by
        rw [← hname_dt', heq, hname_dtn]
      have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [← hname_dt']
        exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
      obtain ⟨hg_eq, hargs_eq⟩ :=
        hunique hconc g_orig g_new_orig args args_new heq1 hKey1
      rw [hg_eq] at hdt_orig_get
      rw [hdt_new_get] at hdt_orig_get
      have hdt_orig_eq : dt_orig = dt_new_orig := by
        have h1 : Typed.Declaration.dataType dt_new_orig =
            .dataType dt_orig := Option.some.inj hdt_orig_get
        injection h1.symm
      apply hne
      rw [hshape, hshape_new, hg_eq, hargs_eq, hdt_orig_eq]
    obtain ⟨md_dt_at, hmd_at_get_dt, _hName_dt, _hParams_dt, hCtors_dt⟩ :=
      PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
        drained.newFunctions drained.newDataTypes hdt_new_mem
        hDtCtorNotKey hFnNotKey hOtherDtNotKey
    rw [hmd_at_get_dt] at hmd_get
    have hmd_eq : md_dt_at = md_dt := by
      have h1 : Typed.Declaration.dataType md_dt_at = .dataType md_dt :=
        Option.some.inj hmd_get
      injection h1
    rw [hmd_eq] at hCtors_dt
    -- hCtors_dt : md_dt.constructors = dt_new.constructors.map (rewriteTyp ∅ drained.mono).
    -- Identify md_c with rewritten counterpart.
    have hmd_c_eq_rew :
        md_c ∈ dt_new.constructors.map (fun c0 =>
          { c0 with argTypes := c0.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }) := by
      rw [← hCtors_dt]
      show md_dt.constructors[i]'hi_lt_md ∈ md_dt.constructors
      exact List.getElem_mem hi_lt_md
    obtain ⟨c_new, hc_new_mem, hc_new_eq⟩ := List.mem_map.mp hmd_c_eq_rew
    have hmc_at : md_c.argTypes =
        c_new.argTypes.map (rewriteTyp (fun _ => none) drained.mono) := by
      rw [← hc_new_eq]
    have hj_lt_cnew : j < c_new.argTypes.length := by
      have hLenEq : md_c.argTypes.length = c_new.argTypes.length := by
        rw [hmc_at]; exact List.length_map ..
      rw [hLenEq] at hj_lt_md_at; exact hj_lt_md_at
    let cnew_t : Typ := c_new.argTypes[j]'hj_lt_cnew
    have hmd_t_eq : md_t = rewriteTyp (fun _ => none) drained.mono cnew_t := by
      show md_c.argTypes[j]'hj_lt_md_at = rewriteTyp (fun _ => none) drained.mono cnew_t
      have hLenEq : md_c.argTypes.length = c_new.argTypes.length := by
        rw [hmc_at]; exact List.length_map ..
      rw [List.getElem_of_eq hmc_at hj_lt_md_at]
      show (c_new.argTypes.map (rewriteTyp (fun _ => none) drained.mono))[j]'(by
              rw [List.length_map]; rw [hLenEq] at hj_lt_md_at; exact hj_lt_md_at)
          = rewriteTyp (fun _ => none) drained.mono (c_new.argTypes[j]'hj_lt_cnew)
      simp [List.getElem_map]
    -- Trace c_new back to source dt_orig.constructors via NewDtFullShape.
    obtain ⟨g_orig, args_orig, dt_orig, _hin_seen, hdt_orig_get, hsz, hdt_new_shape⟩ :=
      hNDFS dt_new hdt_new_mem
    -- dt_new.name = concretizeName g_orig args_orig.
    have hdt_new_name' : dt_new.name = concretizeName g_orig args_orig := by
      rw [hdt_new_shape]
    -- dt_new.constructors via the explicit instantiate-form.
    have hdt_new_ctors : dt_new.constructors =
        dt_orig.constructors.map (fun c0 =>
          ({ c0 with argTypes :=
            c0.argTypes.map (Typ.instantiate (mkParamSubst dt_orig.params args_orig)) }
            : Constructor)) := by
      rw [hdt_new_shape]
    -- Identify c_new with the instantiated counterpart in dt_orig.constructors.
    have hc_new_in : c_new ∈ dt_orig.constructors.map (fun c0 =>
      ({ c0 with argTypes :=
        c0.argTypes.map (Typ.instantiate (mkParamSubst dt_orig.params args_orig)) }
        : Constructor)) := by
      rw [← hdt_new_ctors]; exact hc_new_mem
    obtain ⟨src_c, hsrc_c_mem, hsrc_c_eq⟩ := List.mem_map.mp hc_new_in
    -- c_new.argTypes = src_c.argTypes.map (Typ.instantiate subst).
    let subst := mkParamSubst dt_orig.params args_orig
    have hcnew_at : c_new.argTypes =
        src_c.argTypes.map (Typ.instantiate subst) := by
      rw [← hsrc_c_eq]
    have hj_lt_src : j < src_c.argTypes.length := by
      have hLenEq : c_new.argTypes.length = src_c.argTypes.length := by
        rw [hcnew_at]; exact List.length_map ..
      rw [hLenEq] at hj_lt_cnew; exact hj_lt_cnew
    let src_t : Typ := src_c.argTypes[j]'hj_lt_src
    have hcnew_t_eq : cnew_t = Typ.instantiate subst src_t := by
      show c_new.argTypes[j]'hj_lt_cnew = Typ.instantiate subst src_t
      have hLenEq : c_new.argTypes.length = src_c.argTypes.length := by
        rw [hcnew_at]; exact List.length_map ..
      rw [List.getElem_of_eq hcnew_at hj_lt_cnew]
      show (src_c.argTypes.map (Typ.instantiate subst))[j]'(by
              rw [List.length_map]; rw [hLenEq] at hj_lt_cnew; exact hj_lt_cnew)
          = Typ.instantiate subst (src_c.argTypes[j]'hj_lt_src)
      simp [List.getElem_map]
    -- Source-side rank witness for src_t.
    have hsrc_t_mem : src_t ∈ src_c.argTypes := List.getElem_mem hj_lt_src
    have hbound := hrank_src g_orig dt_orig hdt_orig_get src_c hsrc_c_mem src_t hsrc_t_mem
    obtain ⟨hSRB_src, hPS_src⟩ := hbound
    -- Identify templateName = g_orig (via templateOf + hDrainShape).
    have htemplateName_eq_orig : templateName = g_orig := by
      have h1 := hDrainShape g templateName args_tpl ⟨cdt, hget⟩ hname_tpl
      have h2 := htemplateOf_id g
      rw [h2] at h1
      -- h1 : templateName = g
      -- Now apply hDrainShape with (g_orig, args_orig) producing g.
      have hcN : concretizeName g_orig args_orig = g := by
        rw [← hdt_new_name', hdt_new_name]
      have h3 := hDrainShape g g_orig args_orig ⟨cdt, hget⟩ hcN
      rw [h2] at h3
      rw [h1, h3]
    rw [htemplateName_eq_orig]
    -- Build the cd-side conversion.
    rw [hmd_t_eq, hcnew_t_eq] at hmd_t_to_t
    -- Now hmd_t_to_t : typToConcrete ∅ (rewriteTyp ∅ mono (Typ.instantiate subst src_t)) = .ok t.
    -- ParamSafe constraint on subst: subst maps params to args from args_orig,
    -- which gives `.ref g'` only if `g' ∈ params` — but ParamSafe forbids that
    -- at the top level of src_t. We need a sub-induction that handles
    -- non-trivial subst correctly.
    -- Discharge `hAppRef`: the typed-side `AppRefToDt` invariant
    -- on `dt_orig`'s argTypes — threaded from `spine_transfer`'s sig
    -- via `hAppRefToDt`.
    have hAppRef_src_t : Typed.Typ.AppRefToDt tds dt_orig.params src_t :=
      hAppRefToDt g_orig dt_orig hdt_orig_get src_c hsrc_c_mem src_t hsrc_t_mem
    exact spine_transfer_aux (rank_src := rank_src) (rank_cd := rank_cd)
      (subst := subst) (mono := drained.mono)
      hMonoShape hunique hconc htemplateOf_id
      (params := dt_orig.params) (bd := rank_src g_orig)
      (hsubst_paramSafe := by
        -- subst g' = some _ implies toString g' ∈ params.
        -- mkParamSubst params args_orig builds m by folding insert over
        -- params.zip args.toList; existence at g' implies g' = Global.init p
        -- for some p ∈ params, hence toString g' = p ∈ params.
        -- Dispatched to `Aiur.mkParamSubst_some_implies_param_axiom`.
        -- The `_hIdentParams` premise on the axiom is discharged via the
        -- new `Aiur.dt_params_identifier_axiom`, which asserts that
        -- every typed dataType's params is a list of identifier-like strings
        -- (Aiur parser invariant: type-param names are tokenized as
        -- identifiers, so they satisfy
        --   `p ≠ "" ∧ ¬ p.front.isDigit ∧ all chars alpha/digit/'_'`).
        intro g' ⟨τ, hτ⟩
        show toString g' ∈ dt_orig.params
        -- Discharge `_hSrc` for `dt_params_identifier_axiom` via the
        -- `hdt_orig_get : tds.getByKey g_orig = some (.dataType dt_orig)` witness,
        -- packaged as `⟨g_orig, dt_orig, hdt_orig_get, rfl⟩`.
        exact Aiur.mkParamSubst_some_implies_param_axiom dt_orig.params
          args_orig g' τ
          (Aiur.dt_params_identifier_axiom tds dt_orig.params
            ⟨g_orig, dt_orig, hdt_orig_get, rfl⟩)
          hτ)
      hSRB_src hPS_src
      hAppRef_src_t
      -- Discharge `hsubst_range`: subst = mkParamSubst dt_orig.params args_orig,
      -- so range values are types from args_orig (the call-site type-args).
      -- These were registered in the drain's pending queue via the `.app`
      -- syntactic position; `NewDtFullShape` ties them to a real source-side
      -- emission, and rank-bound + ParamSafe-empty come from the source-side
      -- rank invariant `hrank_src`. Dispatched to
      -- `Aiur.newDt_args_orig_spineRefsBelow_axiom`.
      (hsubst_range := by
        intro g' τ hτ
        exact Aiur.newDt_args_orig_spineRefsBelow_axiom hNDFS hrank_src
          hdt_orig_get hdt_new_mem hdt_new_name' hτ)
      rfl rank_cd_def
      hmd_t_to_t

end DirectDagBody

/-! ### Wire B: entry-restricted concretize ctor-present propagation.

Companion to `concretizeBuild_preserves_function_kind_at_entry_fwd`: under
`WellFormed`-implied hypotheses (typed-side `CtorPresent`, `DtNameIsKey`,
`CtorIsKey`, `ConcretizeUniqueNames`), every `.dataType cdt` pair in the
concretize output `cd` carries every `c ∈ cdt.constructors` as a
`.constructor cdt cc` pair at `cdt.name.pushNamespace c.nameHead`.

Located in SizeBound (not Phase4) so the body can use
`DirectDagBody.concretizeBuild_dataType_origin` (defined above). -/
theorem concretize_produces_ctorPresent_under_entry
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (htdCtorPresent : Typed.Decls.CtorPresent tds)
    (htdDt : Typed.Decls.DtNameIsKey tds)
    (_htdCtor : Typed.Decls.CtorIsKey tds)
    (hUnique : Typed.Decls.ConcretizeUniqueNames tds)
    (hCdDtNameKey : ∀ g dt, cd.getByKey g = some (.dataType dt) → g = dt.name)
    (hconc : tds.concretize = .ok cd) :
    ∀ (dtkey : Global) (dt : Concrete.DataType) (c : Concrete.Constructor),
      (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc,
        (dt.name.pushNamespace c.nameHead,
          Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList := by
  -- Extract drained from hconc.
  have hconc' := hconc
  unfold Typed.Decls.concretize at hconc'
  simp only [bind, Except.bind] at hconc'
  split at hconc'
  · cases hconc'
  rename_i drained hdrain
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
  -- NewDtFullShape preserved through drain (gives full canonical instantiation
  -- form for newDt entries — needed for D3c uniqueness and for kind-collision
  -- discharges at dtkey-level disjointness premises in D2-len/D2e/D2f path).
  have hNewDtFull : drained.NewDtFullShape tds :=
    concretize_drain_preserves_NewDtFullShape _ _
      (DrainState.NewDtFullShape.init tds (concretizeSeed tds)) hdrain
  -- NewFnFullShape preserved through drain (mirror; not strictly needed here
  -- but kept for symmetry).
  have _hNewFnFull : drained.NewFnFullShape tds :=
    concretize_drain_preserves_NewFnFullShape _ _
      (DrainState.NewFnFullShape.init tds (concretizeSeed tds)) hdrain
  intro dtkey cdt c hcd_mem hc_mem
  have hcd_get : cd.getByKey dtkey = some (.dataType cdt) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hcd_mem
  -- Step (A): cd .dataType at dtkey ⟹ monoDecls .dataType at dtkey.
  obtain ⟨md_dt, hmd_get⟩ :=
    step4Lower_backward_dataType_kind_at_key hcd_get hconc'
  -- Step (B): explicit length + nameHead correspondence between cdt and md_dt.
  obtain ⟨cdt', hcd_get', hKeyName', hLen, hPosNH, hCtorsDt⟩ :=
    step4Lower_dataType_explicit hmd_get hconc'
  rw [hcd_get] at hcd_get'
  cases hcd_get'
  -- Step (C): identify position i of c in cdt.constructors.
  obtain ⟨i, hi_lt_cdt, hi_eq⟩ := List.getElem_of_mem hc_mem
  have hi_lt_md : i < md_dt.constructors.length := by rw [hLen] at hi_lt_cdt; exact hi_lt_cdt
  have hnh : c.nameHead = (md_dt.constructors[i]'hi_lt_md).nameHead := by
    have hpos := hPosNH i hi_lt_md hi_lt_cdt
    rw [← hi_eq]; exact hpos
  -- Step (D): origin split for md_dt — typed source-side (params=[]) OR drain newDataTypes.
  have horigin :=
    DirectDagBody.concretizeBuild_dataType_origin tds drained.mono
      drained.newFunctions drained.newDataTypes hmd_get
  -- (D-name) cdt.name = md_dt.name — closed via strengthened
  -- `step4Lower_dataType_explicit` (D1 ✓).
  have hKeyName : cdt.name = md_dt.name := hKeyName'
  let c_md : Constructor := md_dt.constructors[i]'hi_lt_md
  have hKeyEq :
      cdt.name.pushNamespace c.nameHead = md_dt.name.pushNamespace c_md.nameHead := by
    show cdt.name.pushNamespace c.nameHead =
      md_dt.name.pushNamespace (md_dt.constructors[i]'hi_lt_md).nameHead
    rw [hKeyName, hnh]
  -- Step (E): mono-side `.constructor md_dt md_c` at the pushed key.
  have hmd_ctor :
      ∃ md_c, (concretizeBuild tds drained.mono drained.newFunctions
        drained.newDataTypes).getByKey
          (md_dt.name.pushNamespace c_md.nameHead) = some (.constructor md_dt md_c) := by
    rcases horigin with ⟨td_dt, htd_get, htd_params⟩ | ⟨dt', hmem, hname⟩
    · -- Typed-origin closure (D2). tds .dataType at dtkey with empty params.
      -- Step D2-1: htdDt forces dtkey = td_dt.name.
      have htd_mem : (dtkey, Typed.Declaration.dataType td_dt) ∈ tds.pairs.toList :=
        IndexMap.mem_pairs_of_getByKey _ _ _ htd_get
      have hDtkeyEq : dtkey = td_dt.name := htdDt _ _ htd_mem
      have hdtkey_in_cd : ∃ d, cd.getByKey dtkey = some d := ⟨_, hcd_get⟩
      -- D2-STRUCT: derive md_dt's explicit structure
      --   md_dt = { name := dtkey, params := [],
      --             constructors := td_dt.constructors.map
      --               (fun c => { c with argTypes := c.argTypes.map
      --                 (rewriteTyp (fun _ => none) drained.mono) }) }
      -- via case-split on whether some newDt has name=dtkey (override). Both
      -- cases produce the same explicit form (see analysis: dtStep override
      -- uses NewDtFullShape's mkParamSubst[]#[] = identity, then dtStep applies
      -- the SAME `rewriteTyp empty mono`).
      -- The "rewritten constructors" form (used in both Case A and Case B closure).
      -- Defined as a separate `let` to avoid parser issues with structure-update
      -- containing nested `.map` calls.
      let rewrittenCtors_td : List Constructor :=
        List.map (fun c : Constructor =>
          { c with argTypes := List.map (rewriteTyp (fun _ => none) drained.mono) c.argTypes })
          td_dt.constructors
      have hmdEq_struct : md_dt = { td_dt with constructors := rewrittenCtors_td } := by
        -- Subroutine: derive disjointness premises for either branch.
        by_cases hOverride : ∃ dt'' ∈ drained.newDataTypes, dt''.name = dtkey
        · -- Case B: some newDt has name=dtkey. Use NewDtFullShape to identify
          -- dt''.constructors = td_dt.constructors (struct-eta). Then apply
          -- `concretizeBuild_at_newDt_name_full_explicit`.
          obtain ⟨dt'', hdt''_mem, hdt''_name⟩ := hOverride
          obtain ⟨g_d, args_d, dt_orig_d, _h_seen, hd_get, hd_sz, hd_shape⟩ :=
            hNewDtFull dt'' hdt''_mem
          -- dt''.name = dtkey ⇒ concretizeName g_d args_d = dtkey via hd_shape.
          have hd_name : dt''.name = concretizeName g_d args_d := by rw [hd_shape]
          have heq_concName : concretizeName g_d args_d = concretizeName dtkey #[] := by
            rw [← hd_name, hdt''_name, concretizeName_empty_args]
          have hCdKey : ∃ d, cd.getByKey (concretizeName g_d args_d) = some d := by
            rw [heq_concName, concretizeName_empty_args]; exact hdtkey_in_cd
          obtain ⟨hg_eq, hargs_eq⟩ :=
            hUnique hconc g_d dtkey args_d #[] heq_concName hCdKey
          -- dt_orig_d = td_dt by tds key uniqueness at dtkey.
          rw [hg_eq] at hd_get
          have hdt_orig_eq : dt_orig_d = td_dt := by
            have hcomb := hd_get.symm.trans htd_get
            simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hcomb
            exact hcomb
          -- Disjointness premises for dt''.name = dtkey.
          have hDtCtorNotKey_dt'' :
              ∀ dt''' ∈ drained.newDataTypes, ∀ c ∈ dt'''.constructors,
                dt'''.name.pushNamespace c.nameHead ≠ dt''.name := by
            intro dt''' hdt'''_mem c'' hc'' heq
            let collisionArg : Typ := .ref ⟨.mkSimple c''.nameHead⟩
            have hLHS_eq : concretizeName dt'''.name #[collisionArg] =
                dt'''.name.pushNamespace c''.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt'''.name c''.nameHead
            have heq_concName' :
                concretizeName dt'''.name #[collisionArg] = concretizeName dtkey #[] := by
              rw [hLHS_eq, heq, hdt''_name, concretizeName_empty_args]
            have hKey_in_cd' :
                ∃ d, cd.getByKey (concretizeName dt'''.name #[collisionArg]) = some d := by
              rw [hLHS_eq, heq, hdt''_name]; exact hdtkey_in_cd
            obtain ⟨_h, hargs_eq'⟩ :=
              hUnique hconc dt'''.name dtkey #[collisionArg] #[] heq_concName' hKey_in_cd'
            have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
            have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq']; rfl
            omega
          have hFnNotKey_dt'' :
              ∀ f ∈ drained.newFunctions, f.name ≠ dt''.name := by
            intro f hf heq
            obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
            have heq' : concretizeName g_f args_f = concretizeName dtkey #[] := by
              rw [← hf_name, heq, hdt''_name, concretizeName_empty_args]
            have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
              rw [heq', concretizeName_empty_args]; exact hdtkey_in_cd
            obtain ⟨hg_eq', _⟩ :=
              hUnique hconc g_f dtkey args_f #[] heq' hKey_in_cd
            rw [hg_eq'] at hf_get
            rw [htd_get] at hf_get; cases hf_get
          have hOtherDtNotKey_dt'' :
              ∀ dt''' ∈ drained.newDataTypes, dt''' ≠ dt'' → dt'''.name ≠ dt''.name := by
            -- NewDtFullShape uniqueness, mirror D3c closure.
            intro dt''' hdt'''_mem hne heq
            obtain ⟨g_d''', args_d''', dt_orig_d''', _h_seen''', hd_get''', _hd_sz''',
                    hd_shape'''⟩ := hNewDtFull dt''' hdt'''_mem
            have hd_name''' : dt'''.name = concretizeName g_d''' args_d''' := by
              rw [hd_shape''']
            have heq_concName' :
                concretizeName g_d''' args_d''' = concretizeName g_d args_d := by
              rw [← hd_name''', heq, hd_name]
            have hCdKey' : ∃ d,
                cd.getByKey (concretizeName g_d''' args_d''') = some d := by
              refine ⟨.dataType cdt, ?_⟩
              rw [heq_concName', ← hd_name, hdt''_name]; exact hcd_get
            obtain ⟨hg_eq', hargs_eq'⟩ :=
              hUnique hconc g_d''' g_d args_d''' args_d heq_concName' hCdKey'
            rw [hg_eq', hg_eq] at hd_get'''
            -- Now hd_get''' : tds.getByKey dtkey = some (.dataType dt_orig_d''')
            have hdt_orig_eq' : dt_orig_d''' = dt_orig_d := by
              have hcomb := hd_get'''.symm.trans hd_get
              simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hcomb
              exact hcomb
            rw [hd_shape, hd_shape'''] at hne
            rw [hg_eq', hargs_eq', hdt_orig_eq'] at hne
            exact hne rfl
          -- Apply concretizeBuild_at_newDt_name_full_explicit to get md_dt
          -- structure with dt''.constructors mapped via rewriteTyp empty mono.
          obtain ⟨md_dt', hbuild', hMdName', hMdParams', hCtors'⟩ :=
            PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
              drained.newFunctions drained.newDataTypes hdt''_mem
              hDtCtorNotKey_dt'' hFnNotKey_dt'' hOtherDtNotKey_dt''
          -- Identify md_dt' = md_dt at dtkey.
          rw [hdt''_name] at hbuild'
          rw [hbuild'] at hmd_get
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hmd_get
          -- hmd_get : md_dt' = md_dt
          rw [← hmd_get]
          -- Now show md_dt' = { td_dt with constructors := ... }.
          -- md_dt'.name = dt''.name = dtkey; md_dt'.constructors = dt''.constructors.map ....
          -- We need to show dt''.constructors = td_dt.constructors structurally
          -- via NewDtFullShape's hd_shape and Typ.instantiate_empty_id.
          have hsz_args : args_d.size = 0 := by rw [hargs_eq]; rfl
          rw [hsz_args] at hd_sz
          -- dt_orig_d.params.length = 0 ⇒ dt_orig_d.params = [].
          have hparams_empty : dt_orig_d.params = [] := List.length_eq_zero_iff.mp hd_sz.symm
          -- mkParamSubst dt_orig_d.params args_d = mkParamSubst [] #[] = (fun _ => none).
          have hsubst_empty :
              mkParamSubst dt_orig_d.params args_d = (fun _ => none) := by
            unfold mkParamSubst
            rw [hparams_empty, hargs_eq]
            simp
          -- Now compute dt''.constructors structurally.
          have hat_id : ∀ (ts : List Typ),
              ts.map (Typ.instantiate (fun _ => none)) = ts := by
            intro ts
            induction ts with
            | nil => rfl
            | cons t rest' ih' =>
              simp only [List.map_cons]
              rw [Typ.instantiate_empty_id, ih']
          have hctor_id : ∀ (cs : List Constructor),
              List.map (fun c : Constructor =>
                  let new_at := List.map (Typ.instantiate (fun _ => none)) c.argTypes
                  ({ c with argTypes := new_at } : Constructor)) cs = cs := by
            intro cs
            induction cs with
            | nil => rfl
            | cons c rest ih =>
              simp only [List.map_cons, List.cons.injEq]
              refine ⟨?_, ih⟩
              -- Show: { c with argTypes := c.argTypes.map (Typ.instantiate ...) } = c.
              cases c with
              | mk nameHead argTypes =>
                simp only
                rw [hat_id]
          have hdt''_ctors : dt''.constructors = td_dt.constructors := by
            rw [hd_shape, hdt_orig_eq]
            -- Goal: { name := concretizeName g_d args_d, params := [],
            --        constructors := td_dt.constructors.map (fun c => ...) }.constructors
            --       = td_dt.constructors.
            -- After projection: td_dt.constructors.map (...) = td_dt.constructors.
            have hsubst_td : mkParamSubst td_dt.params args_d = (fun _ => none) := by
              rw [← hdt_orig_eq]; exact hsubst_empty
            simp only [hsubst_td]
            exact hctor_id td_dt.constructors
          have hdt''_name_eq : dt''.name = td_dt.name := by
            rw [← hDtkeyEq, hdt''_name]
          have hdt''_params : dt''.params = [] := by
            rw [hd_shape]
          -- Now md_dt'.name = dt''.name = td_dt.name and md_dt'.constructors =
          -- dt''.constructors.map (rewriteTyp empty mono) = td_dt.constructors.map (...).
          have hMdName_td : md_dt'.name = td_dt.name := by
            rw [hMdName', hdt''_name_eq]
          have hMdParams_td : md_dt'.params = td_dt.params := by
            rw [hMdParams', hdt''_params, htd_params]
          have hMdCtors_td : md_dt'.constructors = rewrittenCtors_td := by
            show md_dt'.constructors = rewrittenCtors_td
            rw [hCtors', hdt''_ctors]
          -- DataType structural equality via mk-injEq (no @[ext]).
          show md_dt' = { td_dt with constructors := rewrittenCtors_td }
          cases md_dt' with
          | mk name params constructors =>
            simp only at hMdName_td hMdParams_td hMdCtors_td
            cases td_dt with
            | mk tname tparams tctors =>
              simp only [DataType.mk.injEq]
              simp only at hMdName_td hMdParams_td hMdCtors_td htd_params
              exact ⟨hMdName_td, hMdParams_td, hMdCtors_td⟩
        · -- Case A: no newDt has name=dtkey. Apply
          -- concretizeBuild_at_typed_dataType_explicit.
          have hDtNotKey_dtkey : ∀ dt'' ∈ drained.newDataTypes, dt''.name ≠ dtkey := by
            intro dt'' hdt'' heq
            exact hOverride ⟨dt'', hdt'', heq⟩
          have hFnNotKey_dtkey : ∀ f ∈ drained.newFunctions, f.name ≠ dtkey := by
            intro f hf heq
            obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
            have heq' : concretizeName g_f args_f = concretizeName dtkey #[] := by
              rw [← hf_name, heq, concretizeName_empty_args]
            have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
              rw [heq', concretizeName_empty_args]; exact hdtkey_in_cd
            obtain ⟨hg_eq, _hargs_eq⟩ :=
              hUnique hconc g_f dtkey args_f #[] heq' hKey_in_cd
            rw [hg_eq] at hf_get
            rw [htd_get] at hf_get; cases hf_get
          have hCtorNotKey_dtkey : ∀ dt'' ∈ drained.newDataTypes,
              ∀ c'' ∈ dt''.constructors, dt''.name.pushNamespace c''.nameHead ≠ dtkey := by
            intro dt'' hdt''_mem c'' hc'' heq
            let collisionArg : Typ := .ref ⟨.mkSimple c''.nameHead⟩
            have hLHS_eq : concretizeName dt''.name #[collisionArg] =
                dt''.name.pushNamespace c''.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt''.name c''.nameHead
            have heq_concName :
                concretizeName dt''.name #[collisionArg] = concretizeName dtkey #[] := by
              rw [hLHS_eq, heq, concretizeName_empty_args]
            have hKey_in_cd' :
                ∃ d, cd.getByKey (concretizeName dt''.name #[collisionArg]) = some d := by
              rw [hLHS_eq, heq]; exact hdtkey_in_cd
            obtain ⟨_, hargs_eq⟩ :=
              hUnique hconc dt''.name dtkey #[collisionArg] #[] heq_concName hKey_in_cd'
            have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
            have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
            omega
          have hbuild_dt :=
            PhaseA2.concretizeBuild_at_typed_dataType_explicit tds drained.mono
              drained.newFunctions drained.newDataTypes
              (g := dtkey) (td_dt := td_dt)
              htd_get htd_params
              hDtNotKey_dtkey hFnNotKey_dtkey hCtorNotKey_dtkey
          simp only at hbuild_dt
          rw [hmd_get] at hbuild_dt
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hbuild_dt
          -- After simp, hbuild_dt : md_dt = { td_dt with constructors := td_dt.constructors.map (rewriteTyp ...) }
          -- Goal: md_dt = { td_dt with constructors := rewrittenCtors_td } (definitionally same).
          rw [show (rewrittenCtors_td : List Constructor) =
              td_dt.constructors.map (fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) })
              from rfl]
          exact hbuild_dt
      -- Step D2-2: pick c' = td_dt.constructors[i].
      have hi_lt_td : i < td_dt.constructors.length := by
        have hLen' : md_dt.constructors.length = td_dt.constructors.length := by
          rw [hmdEq_struct]
          show rewrittenCtors_td.length = td_dt.constructors.length
          exact List.length_map ..
        rw [hLen'] at hi_lt_md; exact hi_lt_md
      let c' : Constructor := td_dt.constructors[i]'hi_lt_td
      have hc'_mem : c' ∈ td_dt.constructors := List.getElem_mem hi_lt_td
      -- Step D2-3: htdCtorPresent yields a typed ctor entry.
      obtain ⟨td_c, htd_ctor_mem⟩ := htdCtorPresent dtkey td_dt c' htd_mem hc'_mem
      have htd_ctor_get : tds.getByKey (td_dt.name.pushNamespace c'.nameHead) =
          some (.constructor td_dt td_c) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ htd_ctor_mem
      -- Step D2-4: disjointness premises.
      let g : Global := td_dt.name.pushNamespace c'.nameHead
      -- cd has g (= K, the typed ctor key) — derive via cd-side preservation.
      -- htdCtorPresent gives typed ctor at g. concretize_produces_ctorPresent_under_entry
      -- (this very theorem) produces cd ctor at g. CIRCULAR — instead use the
      -- cd-side existence indirectly via hcd_get + step4Lower.
      -- Direct route: in Or.inl branch of horigin, no drain entry has
      -- name=dtkey, but K = dtkey.pushNs c'.nameHead is a different key. Apply
      -- hUnique with cd witness at the typed ctor key g via an alternative
      -- derivation: g IS keyed in cd (via htdCtorPresent post-concretize),
      -- but proving this needs the very theorem we're proving. Instead, we
      -- exploit that g is keyed in tds (typed ctor) and use kind-uniqueness
      -- WITHOUT a cd witness: if dt''.name = g, then by hSNN.2 dt''.name =
      -- concretizeName g_d args_d. We need a cd witness for hUnique to apply.
      have hg_in_cd : ∃ d, cd.getByKey g = some d := by
        -- g is a typed source ctor key. fromSource srcStep at g inserts a
        -- `.constructor` (under td_dt.params = []). Subsequent dtStep / fnStep
        -- folds may override but each always produces SOME value at g (insert).
        -- step4Lower preserves the key as a cd entry.
        -- Stage 1: monoDecls = concretizeBuild has g as key.
        have hmono_has_g : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).getByKey g = some d := by
          rw [PhaseA2.concretizeBuild_eq]
          -- fromSource inserts .ctor at g under td_dt.params=[].
          obtain ⟨md_dt, md_c, h_src⟩ :=
            PhaseA2.fromSource_inserts_ctor_at_key tds drained.mono htd_ctor_get htd_params
          -- Now any subsequent dtStep / fnStep insert preserves SOME value at g.
          -- We need a generic foldl-preservation: each step's result has g iff
          -- the prior accumulator has g.
          -- Apply Array.foldl_induction with motive `∃ d, acc.getByKey g = some d`.
          have hfn_pres_some : ∀ (acc : Typed.Decls) (f : Typed.Function),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey g = some d := by
            intro acc f ⟨d, hget⟩
            unfold PhaseA2.fnStep
            by_cases hbeq : (f.name == g) = true
            · have hkeq : f.name = g := LawfulBEq.eq_of_beq hbeq
              rw [hkeq]
              exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
            · have hne : (f.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
              exact ⟨d, by
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
          -- Generic insert preserves "some at g".
          have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (acc.insert k v).getByKey g = some d := by
            intro acc k v ⟨d, hget⟩
            by_cases hbeq : (k == g) = true
            · have hkeq : k = g := LawfulBEq.eq_of_beq hbeq
              rw [hkeq]; exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
            · have hne : (k == g) = false := Bool.not_eq_true _ |>.mp hbeq
              exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
          have hdt_inner_pres_some : ∀ (acc : Typed.Decls) (newDt : DataType)
              (dt_outer : DataType) (cs : List Constructor),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (cs.foldl
                (fun acc'' c =>
                  acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                    (.constructor newDt c)) acc).getByKey g = some d := by
            intro acc newDt dt_outer cs hacc
            induction cs generalizing acc with
            | nil => exact hacc
            | cons c rest ih =>
              simp only [List.foldl_cons]
              apply ih
              exact hinsert_pres acc _ _ hacc
          have hdt_pres_some : ∀ (acc : Typed.Decls) (dt' : DataType),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey g = some d := by
            intro acc dt' hacc
            simp only [PhaseA2.dtStep]
            apply hdt_inner_pres_some
            exact hinsert_pres acc _ _ hacc
          have hdt_fold_some : ∀ (init : Typed.Decls),
              (∃ d, init.getByKey g = some d) →
              ∃ d, (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono) init).getByKey g
                = some d := by
            intro init hinit
            apply Array.foldl_induction
              (motive := fun (_ : Nat) (acc : Typed.Decls) =>
                ∃ d, acc.getByKey g = some d) hinit
            intro i acc hacc
            exact hdt_pres_some acc _ hacc
          have hfn_fold_some : ∀ (init : Typed.Decls),
              (∃ d, init.getByKey g = some d) →
              ∃ d, (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey g
                = some d := by
            intro init hinit
            apply Array.foldl_induction
              (motive := fun (_ : Nat) (acc : Typed.Decls) =>
                ∃ d, acc.getByKey g = some d) hinit
            intro i acc hacc
            exact hfn_pres_some acc _ hacc
          have hsrc_fold : ∃ d, (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono)
              default).getByKey g = some d := ⟨_, h_src⟩
          have hwithDt := hdt_fold_some _ hsrc_fold
          exact hfn_fold_some _ hwithDt
        -- Stage 2: lift monoDecls .key g to cd .key g via step4Lower.
        obtain ⟨d_mono, hmono_get⟩ := hmono_has_g
        have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
        cases d_mono with
        | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
        | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
        | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
      have hDtNotKey : ∀ dt'' ∈ drained.newDataTypes, dt''.name ≠ g := by
        intro dt'' hdt'' heq
        obtain ⟨g_d, args_d, dt_orig, hd_name, hd_get, _hd_sz, _hd_ctors⟩ :=
          hSNN.2 dt'' hdt''
        have heq' : concretizeName g_d args_d = concretizeName g #[] := by
          rw [← hd_name, heq, concretizeName_empty_args]
        have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_d args_d) = some d := by
          rw [heq', concretizeName_empty_args]; exact hg_in_cd
        obtain ⟨hg_eq, _hargs_eq⟩ :=
          hUnique hconc g_d g args_d #[] heq' hKey_in_cd
        rw [hg_eq] at hd_get
        rw [htd_ctor_get] at hd_get; cases hd_get
      have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
        intro f hf heq
        obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
        have heq' : concretizeName g_f args_f = concretizeName g #[] := by
          rw [← hf_name, heq, concretizeName_empty_args]
        have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
          rw [heq', concretizeName_empty_args]; exact hg_in_cd
        obtain ⟨hg_eq, _hargs_eq⟩ :=
          hUnique hconc g_f g args_f #[] heq' hKey_in_cd
        rw [hg_eq] at hf_get
        rw [htd_ctor_get] at hf_get; cases hf_get
      have hCtorNotKey : ∀ dt'' ∈ drained.newDataTypes, ∀ c'' ∈ dt''.constructors,
          dt''.name.pushNamespace c''.nameHead ≠ g := by
        -- Closed via collision-witness pattern (same as A.1 ctor arm).
        -- pushNamespace s = concretizeName g #[.ref ⟨.mkSimple s⟩] (single-limb appendNameLimbs).
        -- hUnique forces #[collisionArg] = #[], size mismatch.
        intro dt'' hdt''_mem c'' hc'' heq
        let collisionArg : Typ := .ref ⟨.mkSimple c''.nameHead⟩
        have hLHS_eq : concretizeName dt''.name #[collisionArg] =
            dt''.name.pushNamespace c''.nameHead :=
          RefClosedBody.concretizeName_singleton_ref_simple dt''.name c''.nameHead
        have heq_concName :
            concretizeName dt''.name #[collisionArg] = concretizeName g #[] := by
          rw [hLHS_eq, heq, concretizeName_empty_args]
        have hKey_in_cd' :
            ∃ d, cd.getByKey (concretizeName dt''.name #[collisionArg]) = some d := by
          rw [hLHS_eq, heq]; exact hg_in_cd
        obtain ⟨_hname_eq, hargs_eq⟩ :=
          hUnique hconc dt''.name g #[collisionArg] #[] heq_concName hKey_in_cd'
        have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
        have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
        omega
      -- Step D2-5: apply concretizeBuild_at_typed_ctor_explicit.
      have hbuild :=
        PhaseA2.concretizeBuild_at_typed_ctor_explicit tds drained.mono
          drained.newFunctions drained.newDataTypes
          htd_ctor_get htd_params hDtNotKey hFnNotKey hCtorNotKey
      simp only at hbuild
      -- hbuild : (concretizeBuild ...).getByKey g = some (.constructor monoDt monoC)
      -- with monoDt = `{ td_dt with constructors := rewrittenCtors }`,
      --      monoC = `{ td_c with argTypes := rewritten }`.
      -- Step D2-6: identify monoDt = md_dt and align keys.
      have hKey : td_dt.name.pushNamespace c'.nameHead =
          md_dt.name.pushNamespace c_md.nameHead := by
        show td_dt.name.pushNamespace c'.nameHead =
          md_dt.name.pushNamespace (md_dt.constructors[i]'hi_lt_md).nameHead
        -- D2d ✓ CLOSED via cd-side DtNameIsKey + D1 (cdt.name = md_dt.name).
        -- hCdDtNameKey applied to cdt at dtkey: dtkey = cdt.name.
        -- htdDt applied to (dtkey, .dataType td_dt) ∈ tds: dtkey = td_dt.name.
        -- D1 (hKeyName): cdt.name = md_dt.name.
        -- Hence md_dt.name = cdt.name = dtkey = td_dt.name.
        have hMdName : md_dt.name = td_dt.name := by
          have hCdName : dtkey = cdt.name := hCdDtNameKey dtkey cdt hcd_get
          have hTdName : dtkey = td_dt.name := htdDt _ _ htd_mem
          rw [← hKeyName, ← hCdName, hTdName]
        -- c_md.nameHead = td_dt.constructors[i].nameHead = c'.nameHead.
        have hNH : (md_dt.constructors[i]'hi_lt_md).nameHead = c'.nameHead := by
          -- Use hmdEq_struct: md_dt.constructors = td_dt.constructors.map (fun c => {c with argTypes := ...}).
          -- Hence md_dt.constructors[i].nameHead = td_dt.constructors[i].nameHead = c'.nameHead.
          show (md_dt.constructors[i]'hi_lt_md).nameHead = (td_dt.constructors[i]'hi_lt_td).nameHead
          have hmdC_eq : md_dt.constructors[i]'hi_lt_md =
              { (td_dt.constructors[i]'hi_lt_td) with
                argTypes := (td_dt.constructors[i]'hi_lt_td).argTypes.map
                  (rewriteTyp (fun _ => none) drained.mono) } := by
            -- Use hmdEq_struct to identify md_dt.constructors with rewrittenCtors_td.
            have h1 : md_dt.constructors = rewrittenCtors_td := by
              rw [hmdEq_struct]
            -- rewrittenCtors_td[i] = { td_dt.constructors[i] with argTypes := ... }.
            show md_dt.constructors[i]'hi_lt_md = _
            rw [show md_dt.constructors[i]'hi_lt_md = rewrittenCtors_td[i]'(by
                  rw [← h1]; exact hi_lt_md) from by congr 1 <;> exact h1]
            show rewrittenCtors_td[i]'_ = _
            -- rewrittenCtors_td = td_dt.constructors.map f, so [i] = f td_dt.constructors[i].
            simp only [rewrittenCtors_td, List.getElem_map]
          rw [hmdC_eq]
        rw [hMdName, hNH]
      rw [hKey] at hbuild
      -- hbuild : ... = some (.constructor monoDt monoC) where monoDt = md_dt by hmdEq_struct.
      have hmd_unfold : md_dt = DataType.mk td_dt.name td_dt.params
          (List.map (fun c : Constructor =>
            Constructor.mk c.nameHead
              (List.map (rewriteTyp (fun _ => none) drained.mono) c.argTypes))
            td_dt.constructors) := by
        show md_dt = ({ td_dt with constructors := rewrittenCtors_td } : DataType)
        exact hmdEq_struct
      rw [hmd_unfold] at hbuild ⊢
      exact ⟨_, hbuild⟩
    · -- Drain-origin closure (D3). dt' ∈ drained.newDataTypes with dt'.name = dtkey.
      -- The 3 leaf disjointness premises (pushNamespace vs concretizeName
      -- non-collision) remain BLOCKED as named sub-sorries below.
      -- Step D3-1: concretizeBuild_at_newDt_name_explicit identifies md_dt's
      -- structure (length + per-pos nameHead correspondence with dt').
      have hDtCtorNotKey :
          ∀ dt'' ∈ drained.newDataTypes, ∀ c'' ∈ dt''.constructors,
            dt''.name.pushNamespace c''.nameHead ≠ dt'.name := by
        -- Closed via collision-witness pattern (same as A.1 h_cdAt_newDt).
        intro dt'' hdt''_mem c'' hc'' heq
        obtain ⟨g_d, args_d, dt_orig_d, hd_name, hd_get, hd_sz, _hd_ctors⟩ :=
          hSNN.2 dt' hmem
        let collisionArg : Typ := .ref ⟨.mkSimple c''.nameHead⟩
        have hLHS_eq : concretizeName dt''.name #[collisionArg] =
            dt''.name.pushNamespace c''.nameHead :=
          RefClosedBody.concretizeName_singleton_ref_simple dt''.name c''.nameHead
        have heq_concName :
            concretizeName dt''.name #[collisionArg] = concretizeName g_d args_d := by
          rw [hLHS_eq, heq, hd_name]
        have hCdKey :
            ∃ d, cd.getByKey (concretizeName dt''.name #[collisionArg]) = some d := by
          refine ⟨.dataType cdt, ?_⟩
          rw [hLHS_eq, heq, hname]; exact hcd_get
        obtain ⟨hname_dt''_eq, hargs_witness⟩ :=
          hUnique hconc dt''.name g_d #[collisionArg] args_d heq_concName hCdKey
        have hsz_args : args_d.size = 1 := by rw [← hargs_witness]; rfl
        obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name, hdt'_get, hdt'_sz, _⟩ :=
          hSNN.2 dt'' hdt''_mem
        have heq2 : concretizeName g'_orig args'_dt = concretizeName g_d #[] := by
          rw [← hdt'_name, hname_dt''_eq, concretizeName_empty_args]
        have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
          rw [← hdt'_name]
          exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt''_mem
        obtain ⟨_hg'_eq, hargs'_eq⟩ :=
          hUnique hconc g'_orig g_d args'_dt #[] heq2 hKey2
        have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
        rw [hargs'_size] at hdt'_sz
        rw [_hg'_eq, hd_get] at hdt'_get
        have hdt_orig_eq : dt'_orig = dt_orig_d := by
          have h1 : (Typed.Declaration.dataType dt_orig_d) =
              .dataType dt'_orig := Option.some.inj hdt'_get
          injection h1.symm
        rw [hdt_orig_eq] at hdt'_sz
        rw [hsz_args] at hd_sz
        omega
      have hFnNotKey_dt' :
          ∀ f ∈ drained.newFunctions, f.name ≠ dt'.name := by
        intro f hf heq
        -- StrongNewNameShape on f: f.name = concretizeName g_f args_f with
        -- tds .function at g_f.
        obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
        -- StrongNewNameShape on dt': dt'.name = concretizeName g_d args_d with
        -- tds .dataType at g_d.
        obtain ⟨g_d, args_d, dt_orig, hd_name, hd_get, _hd_sz, _hd_ctors⟩ :=
          hSNN.2 dt' hmem
        -- f.name = dt'.name yields concretizeName g_f args_f = concretizeName g_d args_d.
        rw [hf_name, hd_name] at heq
        -- cd has dt'.name (= dtkey) as key — cd.getByKey dtkey = some (.dataType cdt).
        have hCdKey : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
          refine ⟨.dataType cdt, ?_⟩
          rw [heq, ← hd_name, hname]; exact hcd_get
        -- Apply hUnique → g_f = g_d ∧ args_f = args_d.
        obtain ⟨hg_eq, _hargs_eq⟩ := hUnique hconc g_f g_d args_f args_d heq hCdKey
        -- tds has .function at g_f and .dataType at g_d = g_f. IndexMap key
        -- uniqueness: same key → same value, contradicting kind difference.
        rw [hg_eq] at hf_get
        rw [hf_get] at hd_get
        cases hd_get
      have hOtherDtNotKey :
          ∀ dt'' ∈ drained.newDataTypes, dt'' ≠ dt' → dt''.name ≠ dt'.name := by
        -- Closed via NewDtFullShape: each newDt is determined by its push
        -- witness (g, args, dt_orig). Two newDts with the same name share the
        -- same (g, args) by hUnique applied at concretizeName g args =
        -- concretizeName g_d args_d (with cd-key existence at dt'.name = dtkey
        -- via hcd_get + hname). Same (g, args) ⇒ same dt_orig ⇒ same
        -- canonical-instantiation ⇒ dt'' = dt' structurally.
        intro dt'' hdt''_mem hne heq
        obtain ⟨g_d, args_d, dt_orig_d, _h_seen_d, hd_get, hd_sz, hd_shape⟩ :=
          hNewDtFull dt' hmem
        obtain ⟨g_d'', args_d'', dt_orig_d'', _h_seen_d'', hd_get'', hd_sz'',
                hd_shape''⟩ := hNewDtFull dt'' hdt''_mem
        -- dt''.name = dt'.name + canonical-instantiation form gives
        -- concretizeName g_d'' args_d'' = concretizeName g_d args_d.
        have hd_name : dt'.name = concretizeName g_d args_d := by
          rw [hd_shape]
        have hd_name'' : dt''.name = concretizeName g_d'' args_d'' := by
          rw [hd_shape'']
        have heq_concName :
            concretizeName g_d'' args_d'' = concretizeName g_d args_d := by
          rw [← hd_name'', heq, hd_name]
        have hCdKey :
            ∃ d, cd.getByKey (concretizeName g_d'' args_d'') = some d := by
          refine ⟨.dataType cdt, ?_⟩
          rw [heq_concName, ← hd_name, hname]; exact hcd_get
        obtain ⟨hg_eq, hargs_eq⟩ :=
          hUnique hconc g_d'' g_d args_d'' args_d heq_concName hCdKey
        -- Same (g, args) ⇒ same dt_orig (via tds.getByKey g uniqueness).
        rw [hg_eq] at hd_get''
        rw [hd_get''] at hd_get
        have hdt_orig_eq : dt_orig_d'' = dt_orig_d := by
          have h1 : Typed.Declaration.dataType dt_orig_d''
              = .dataType dt_orig_d := Option.some.inj hd_get
          injection h1
        -- Now dt'' and dt' share the same canonical-instantiation form.
        rw [hd_shape, hd_shape''] at hne
        rw [hg_eq, hargs_eq, hdt_orig_eq] at hne
        exact hne rfl
      obtain ⟨md_dt'', hmd_dt''_get, hMdName'', hLen', hPosNH'⟩ :=
        PhaseA2.concretizeBuild_at_newDt_name_explicit tds drained.mono
          drained.newFunctions drained.newDataTypes hmem hDtCtorNotKey
          hFnNotKey_dt' hOtherDtNotKey
      -- Step D3-2: identify md_dt'' = md_dt via IndexMap key uniqueness at dtkey.
      have hMdEq : md_dt'' = md_dt := by
        rw [hname] at hmd_dt''_get
        rw [hmd_dt''_get] at hmd_get
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hmd_get
        exact hmd_get
      -- Step D3-3: pick c_dt' = dt'.constructors[i] (with i < dt'.constructors.length).
      have hi_lt_dt' : i < dt'.constructors.length := by
        rw [← hLen']
        rw [hMdEq]
        exact hi_lt_md
      let c_dt' : Constructor := dt'.constructors[i]'hi_lt_dt'
      have hcdt'_mem : c_dt' ∈ dt'.constructors := List.getElem_mem hi_lt_dt'
      -- nameHead chain: c_md.nameHead = md_dt.constructors[i].nameHead =
      -- dt'.constructors[i].nameHead = c_dt'.nameHead.
      have hNH_chain : c_md.nameHead = c_dt'.nameHead := by
        show (md_dt.constructors[i]'hi_lt_md).nameHead = c_dt'.nameHead
        have hi_lt_md'' : i < md_dt''.constructors.length := by
          rw [hMdEq]; exact hi_lt_md
        have hpos : (md_dt''.constructors[i]'hi_lt_md'').nameHead =
            (dt'.constructors[i]'hi_lt_dt').nameHead := hPosNH' i hi_lt_dt' hi_lt_md''
        have hMdEqi : (md_dt''.constructors[i]'hi_lt_md'').nameHead =
            (md_dt.constructors[i]'hi_lt_md).nameHead := by
          subst hMdEq; rfl
        rw [← hMdEqi]; exact hpos
      -- Step D3-4: concretizeBuild_at_newDt_ctor_name with dt' and c_dt'.
      -- Derive cd has K as key via key-persistence from dtStep emission.
      let K_drain : Global := dt'.name.pushNamespace c_dt'.nameHead
      have hK_drain_in_mono : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
          drained.newDataTypes).getByKey K_drain = some d := by
        rw [PhaseA2.concretizeBuild_eq]
        -- dtStep at dt' (in newDataTypes) inserts `.constructor _ _` at K_drain.
        have hmem' : dt' ∈ drained.newDataTypes.toList := Array.mem_toList_iff.mpr hmem
        obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
        let fromSource_acc := tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default
        -- Process pre, then dt', then post, then fn fold.
        have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
            (∃ d, acc.getByKey K_drain = some d) →
            ∃ d, (acc.insert k v).getByKey K_drain = some d := by
          intro acc k v ⟨d, hget⟩
          by_cases hbeq : (k == K_drain) = true
          · have hkeq : k = K_drain := LawfulBEq.eq_of_beq hbeq
            rw [hkeq]; exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
          · have hne : (k == K_drain) = false := Bool.not_eq_true _ |>.mp hbeq
            exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
        have hinner_pres : ∀ (acc : Typed.Decls) (newDt : DataType)
            (dt_outer : DataType) (cs : List Constructor),
            (∃ d, acc.getByKey K_drain = some d) →
            ∃ d, (cs.foldl
              (fun acc'' c =>
                acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                  (.constructor newDt c)) acc).getByKey K_drain = some d := by
          intro acc newDt dt_outer cs hacc
          induction cs generalizing acc with
          | nil => exact hacc
          | cons c rest ih =>
            simp only [List.foldl_cons]
            apply ih
            exact hinsert_pres acc _ _ hacc
        have hdt_pres : ∀ (acc : Typed.Decls) (dt_x : DataType),
            (∃ d, acc.getByKey K_drain = some d) →
            ∃ d, (PhaseA2.dtStep drained.mono acc dt_x).getByKey K_drain = some d := by
          intro acc dt_x hacc
          simp only [PhaseA2.dtStep]
          apply hinner_pres
          exact hinsert_pres acc _ _ hacc
        have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
            (∃ d, acc.getByKey K_drain = some d) →
            ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey K_drain = some d := by
          intro acc f ⟨d, hget⟩
          unfold PhaseA2.fnStep
          by_cases hbeq : (f.name == K_drain) = true
          · have hkeq : f.name = K_drain := LawfulBEq.eq_of_beq hbeq
            rw [hkeq]; exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
          · have hne : (f.name == K_drain) = false := Bool.not_eq_true _ |>.mp hbeq
            exact ⟨d, by
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
        -- After dtStep at dt': K_drain has value (via dtStep_inserts_ctor_at_self_ctor).
        have hat_dt'_step : ∀ (init : Typed.Decls),
            ∃ d, (PhaseA2.dtStep drained.mono init dt').getByKey K_drain = some d := by
          intro init
          obtain ⟨md_dt, md_c, hget⟩ :=
            PhaseA2.dtStep_inserts_ctor_at_self_ctor drained.mono init dt' hcdt'_mem
          exact ⟨_, hget⟩
        -- Generic foldl preservation for "some at K_drain".
        have hdt_fold_pres : ∀ (xs : List DataType) (init : Typed.Decls),
            (∃ d, init.getByKey K_drain = some d) →
            ∃ d, (xs.foldl (PhaseA2.dtStep drained.mono) init).getByKey K_drain = some d := by
          intro xs
          induction xs with
          | nil => intro init h; exact h
          | cons hd tl ih =>
            intro init h
            simp only [List.foldl_cons]
            exact ih _ (hdt_pres _ _ h)
        have hfn_fold_pres : ∀ (xs : List Typed.Function) (init : Typed.Decls),
            (∃ d, init.getByKey K_drain = some d) →
            ∃ d, (xs.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey K_drain = some d := by
          intro xs
          induction xs with
          | nil => intro init h; exact h
          | cons hd tl ih =>
            intro init h
            simp only [List.foldl_cons]
            exact ih _ (hfn_pres _ _ h)
        -- Compose: pre fold → dt' step → post fold → fn fold.
        repeat rw [← Array.foldl_toList]
        rw [hsplit, List.foldl_append, List.foldl_cons]
        apply hfn_fold_pres
        apply hdt_fold_pres
        exact hat_dt'_step _

      have hK_drain_in_cd : ∃ d, cd.getByKey K_drain = some d := by
        obtain ⟨d_mono, hmono_get⟩ := hK_drain_in_mono
        have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
        cases d_mono with
        | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
        | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
        | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
      have hDtNotKey_K :
          ∀ dt'' ∈ drained.newDataTypes,
            dt''.name ≠ dt'.name.pushNamespace c_dt'.nameHead := by
        -- Closure via NewDtFullShape on BOTH dt'' and dt' + concretizeName-append.
        -- K_drain = dt'.name.pushNamespace c_dt'.nameHead = concretizeName dt'.name
        --   #[.ref ⟨.mkSimple c_dt'.nameHead⟩] (singleton-ref collision).
        -- dt'.name = concretizeName g_d_outer args_d_outer (NewDtFullShape on dt').
        -- Combined: K_drain = concretizeName g_d_outer (args_d_outer.push collisionArg).
        -- dt''.name = concretizeName g_d args_d (NewDtFullShape on dt'').
        -- hUnique: g_d = g_d_outer ∧ args_d = args_d_outer.push collisionArg.
        -- Same g_d ⇒ same dt_orig in tds (key uniqueness). Then size mismatch:
        --   args_d.size = dt_orig.params.length (hd_sz),
        --   args_d.size = args_d_outer.size + 1 = dt_orig.params.length + 1.
        intro dt'' hdt'' heq
        obtain ⟨g_d, args_d, dt_orig, _hd_seen, hd_get, hd_sz, hd_shape⟩ :=
          hNewDtFull dt'' hdt''
        obtain ⟨g_d_outer, args_d_outer, dt_orig_outer, _hd_seen_o, hd_get_o, hd_sz_o,
                hd_shape_o⟩ := hNewDtFull dt' hmem
        let collisionArg : Typ := .ref ⟨.mkSimple c_dt'.nameHead⟩
        have hd_name : dt''.name = concretizeName g_d args_d := by rw [hd_shape]
        have hd_name_o : dt'.name = concretizeName g_d_outer args_d_outer := by rw [hd_shape_o]
        -- K_drain = concretizeName g_d_outer (args_d_outer.push collisionArg).
        have hK_eq : dt'.name.pushNamespace c_dt'.nameHead =
            concretizeName g_d_outer (args_d_outer.push collisionArg) := by
          rw [← RefClosedBody.concretizeName_singleton_ref_simple dt'.name c_dt'.nameHead,
              hd_name_o]
          show concretizeName (concretizeName g_d_outer args_d_outer) #[collisionArg] = _
          unfold concretizeName
          show #[collisionArg].foldl Typ.appendNameLimbs (args_d_outer.foldl Typ.appendNameLimbs g_d_outer) = (args_d_outer.push collisionArg).foldl Typ.appendNameLimbs g_d_outer
          rw [Array.foldl_push]
          rfl
        -- heq_concName: concretizeName g_d args_d = concretizeName g_d_outer (args_d_outer.push collisionArg).
        have heq_concName :
            concretizeName g_d args_d =
              concretizeName g_d_outer (args_d_outer.push collisionArg) := by
          rw [← hd_name, heq, hK_eq]
        have hCdKey :
            ∃ d, cd.getByKey (concretizeName g_d args_d) = some d := by
          rw [← hd_name, heq]; exact hK_drain_in_cd
        obtain ⟨hg_eq, hargs_eq⟩ :=
          hUnique hconc g_d g_d_outer args_d (args_d_outer.push collisionArg)
            heq_concName hCdKey
        -- Same g_d ⇒ dt_orig = dt_orig_outer.
        rw [hg_eq] at hd_get
        have hdt_orig_eq : dt_orig = dt_orig_outer := by
          have hcomb := hd_get.symm.trans hd_get_o
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hcomb
          exact hcomb
        -- Size contradiction.
        have h_sz_lhs : args_d.size = dt_orig.params.length := hd_sz
        have h_sz_rhs : args_d.size = args_d_outer.size + 1 := by
          rw [hargs_eq, Array.size_push]
        have h_sz_outer : args_d_outer.size = dt_orig_outer.params.length := hd_sz_o
        rw [hdt_orig_eq] at h_sz_lhs
        omega
      have hFnNotKey_K :
          ∀ f ∈ drained.newFunctions,
            f.name ≠ dt'.name.pushNamespace c_dt'.nameHead := by
        -- Closure via concretizeName-append + hUnique + tds kind collision.
        -- f.name = concretizeName g_f args_f (hSNN on f) and
        -- K_drain = concretizeName g_d_outer (args_d_outer.push collisionArg).
        -- hUnique forces g_f = g_d_outer; tds .function at g_f vs .dataType at g_d_outer
        -- contradicts.
        intro f hf heq
        obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
        obtain ⟨g_d_outer, args_d_outer, dt_orig_outer, _h_seen_o, hd_get_o, _hd_sz_o,
                hd_shape_o⟩ := hNewDtFull dt' hmem
        let collisionArg : Typ := .ref ⟨.mkSimple c_dt'.nameHead⟩
        have hd_name_o : dt'.name = concretizeName g_d_outer args_d_outer := by rw [hd_shape_o]
        have hK_eq : dt'.name.pushNamespace c_dt'.nameHead =
            concretizeName g_d_outer (args_d_outer.push collisionArg) := by
          rw [← RefClosedBody.concretizeName_singleton_ref_simple dt'.name c_dt'.nameHead,
              hd_name_o]
          show concretizeName (concretizeName g_d_outer args_d_outer) #[collisionArg] = _
          unfold concretizeName
          show #[collisionArg].foldl Typ.appendNameLimbs (args_d_outer.foldl Typ.appendNameLimbs g_d_outer) = (args_d_outer.push collisionArg).foldl Typ.appendNameLimbs g_d_outer
          rw [Array.foldl_push]
          rfl
        have heq_concName :
            concretizeName g_f args_f =
              concretizeName g_d_outer (args_d_outer.push collisionArg) := by
          rw [← hf_name, heq, hK_eq]
        have hCdKey :
            ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
          rw [← hf_name, heq]; exact hK_drain_in_cd
        obtain ⟨hg_eq, _hargs_eq⟩ :=
          hUnique hconc g_f g_d_outer args_f (args_d_outer.push collisionArg)
            heq_concName hCdKey
        rw [hg_eq] at hf_get
        rw [hf_get] at hd_get_o
        cases hd_get_o
      obtain ⟨md_dt''', md_c, hmd_ctor⟩ :=
        PhaseA2.concretizeBuild_at_newDt_ctor_name tds drained.mono
          drained.newFunctions drained.newDataTypes
          (c := c_dt') (dt := dt') hmem hcdt'_mem
          hDtNotKey_K hFnNotKey_K
      -- The ctor entry's dt-companion is md_dt (by uniqueness); package final witness.
      refine ⟨md_c, ?_⟩
      -- Key alignment: md_dt.name.pushNamespace c_md.nameHead =
      -- dt'.name.pushNamespace c_dt'.nameHead.
      have hKey : md_dt.name.pushNamespace c_md.nameHead =
          dt'.name.pushNamespace c_dt'.nameHead := by
        have hMdName : md_dt.name = dt'.name := by
          rw [← hMdEq]; exact hMdName''
        rw [hMdName, hNH_chain]
      rw [hKey]
      -- md_dt''' = md_dt (uniqueness on the .ctor entry: dt-companion is shared).
      -- Use the strengthened concretizeBuild_at_newDt_ctor_name_dt_companion to
      -- get md_dt''' = {dt' with constructors := rewrittenCtors}, AND
      -- concretizeBuild_at_newDt_name_full_explicit to get md_dt = same form.
      -- Helper: the rewritten ctors form for dt'.
      let rewrittenCtors_dt' : List Constructor :=
        List.map (fun c0 : Constructor =>
          { c0 with argTypes := List.map (rewriteTyp (fun _ => none) drained.mono) c0.argTypes })
          dt'.constructors
      have hMd''' : md_dt''' = md_dt := by
        -- Inner-ctor disjointness: ∀ dt'' ∈ newDataTypes, dt'' ≠ dt' →
        --   ∀ c'' ∈ dt''.constructors, dt''.name.pushNs c''.nameHead ≠ K_drain.
        -- By NewDtFullShape uniqueness: dt'' ≠ dt' (with NewDtFullShape) implies
        -- dt''.name ≠ dt'.name (else dt'' = dt'). So dt''.name.pushNs ... has
        -- different prefix from K_drain.
        have hOtherInnerCtorNotKey :
            ∀ dt'' ∈ drained.newDataTypes, dt'' ≠ dt' →
              ∀ c2 ∈ dt''.constructors,
                dt''.name.pushNamespace c2.nameHead ≠ K_drain := by
          intro dt'' hdt''_mem hne c2 hc2 heq
          -- K_drain = dt'.name.pushNs c_dt'.nameHead. heq says dt''.name.pushNs c2.nameHead = K_drain.
          -- By pushNamespace_inj: dt''.name = dt'.name AND c2.nameHead = c_dt'.nameHead.
          have hname_eq : dt''.name = dt'.name := by
            have h' : dt''.name.toName.mkStr c2.nameHead =
                dt'.name.toName.mkStr c_dt'.nameHead := by
              unfold Global.pushNamespace at heq
              exact Global.mk.inj heq
            have h'' : Lean.Name.str dt''.name.toName c2.nameHead =
                Lean.Name.str dt'.name.toName c_dt'.nameHead := h'
            have hname_inner : dt''.name.toName = dt'.name.toName := by injection h''
            -- Use Global eta: g = ⟨g.toName⟩.
            have hf1 : dt''.name = ⟨dt''.name.toName⟩ := rfl
            have hf2 : dt'.name = ⟨dt'.name.toName⟩ := rfl
            rw [hf1, hf2, hname_inner]
          -- Now dt''.name = dt'.name with dt'' ≠ dt'. By hOtherDtNotKey:
          -- dt''.name ≠ dt'.name. Contradiction.
          exact hOtherDtNotKey dt'' hdt''_mem hne hname_eq
        -- Apply concretizeBuild_at_newDt_ctor_name_dt_companion.
        obtain ⟨d_at_K, hd_at_K_get, hD_at_K⟩ :=
          PhaseA2.concretizeBuild_at_newDt_ctor_name_dt_companion tds drained.mono
            drained.newFunctions drained.newDataTypes hmem hcdt'_mem
            hDtNotKey_K hOtherInnerCtorNotKey hFnNotKey_K
        -- hD_at_K : DtCompanionRewrittenFrom drained.mono dt' d_at_K
        -- hd_at_K_get : ... .getByKey (dt'.name.pushNs c_dt'.nameHead) = some d_at_K
        -- Combine with hmd_ctor (gives md_dt''' at same key).
        rw [hd_at_K_get] at hmd_ctor
        simp only [Option.some.injEq] at hmd_ctor
        obtain ⟨md_dt_at_K, md_c_at_K, hd_at_K_eq, hMdAtK_form⟩ := hD_at_K
        rw [hd_at_K_eq] at hmd_ctor
        -- hmd_ctor : .constructor md_dt_at_K md_c_at_K = .constructor md_dt''' md_c
        -- (after simp_only Option some.injEq, the equality is in this direction)
        have hMdEq2 : md_dt''' = md_dt_at_K := by
          have h := hmd_ctor
          injection h with hMdEq2_inner hMcEq2
          exact hMdEq2_inner.symm
        -- hMdAtK_form : md_dt_at_K = {dt' with constructors := rewrittenCtors}
        rw [hMdEq2, hMdAtK_form]
        -- Now goal: {dt' with constructors := ...} = md_dt.
        -- Use concretizeBuild_at_newDt_name_full_explicit to get md_dt's form.
        obtain ⟨md_dt_full, hbuild_full, hMdName_full, hMdParams_full, hCtors_full⟩ :=
          PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hmem hDtCtorNotKey
            hFnNotKey_dt' hOtherDtNotKey
        have hMdFull_eq_md : md_dt_full = md_dt := by
          have h1 : (concretizeBuild tds drained.mono drained.newFunctions
              drained.newDataTypes).getByKey dt'.name =
                some (.dataType md_dt) := by
            rw [hname]; exact hmd_get
          rw [hbuild_full] at h1
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at h1
          exact h1
        rw [← hMdFull_eq_md]
        -- Goal: {dt' with constructors := rewrittenCtors_dt'} = md_dt_full.
        -- md_dt_full has hMdName_full, hMdParams_full, hCtors_full structure.
        have hRC_eq : rewrittenCtors_dt' = md_dt_full.constructors := by
          show List.map _ dt'.constructors = md_dt_full.constructors
          rw [hCtors_full]
        -- Use DataType.mk.injEq.
        cases md_dt_full with
        | mk name params constructors =>
          simp only at hMdName_full hMdParams_full hRC_eq
          show ({ dt' with constructors := rewrittenCtors_dt' } : DataType)
                = { name := name, params := params, constructors := constructors }
          cases dt' with
          | mk dt_name dt_params dt_ctors =>
            simp only at hMdName_full hMdParams_full
            simp only [DataType.mk.injEq]
            exact ⟨hMdName_full.symm, hMdParams_full.symm, hRC_eq⟩
      rw [← hMd''']
      exact hmd_ctor
  obtain ⟨md_c, hmd_ctor_get⟩ := hmd_ctor
  -- Step (F): lift mono .ctor to cd .ctor with explicit ctors witness.
  obtain ⟨cdt'', cc, hcd_ctor_get, hCdtNameEq, _hLen'', _hCh, _hPerPos'', _hPosEq'',
          hCtorsC, _hArgTypesC⟩ :=
    step4Lower_constructor_explicit hmd_ctor_get hconc'
  -- Step (G): identify cdt'' = cdt — both arms of step4Lower compute identical
  -- `md_dt.constructors.mapM (fun c => …)` for the same md_dt; by Except.ok
  -- injectivity the constructors lists agree. Combined with name agreement,
  -- the structural equality follows. (D4 ✓)
  have hCdEq : cdt'' = cdt := by
    -- Concrete.DataType is `{ name, constructors }` — extensionality.
    have hName : cdt''.name = cdt.name := by rw [hCdtNameEq, hKeyName]
    have hCtors : cdt''.constructors = cdt.constructors := by
      -- Both = `md_dt.constructors.mapM (…)`'s `.ok` payload — equal by
      -- Except.ok.injEq.
      have heq : (Except.ok cdt''.constructors
            : Except ConcretizeError (List Concrete.Constructor)) =
          Except.ok cdt.constructors := by
        rw [← hCtorsC, ← hCtorsDt]
      exact (Except.ok.injEq _ _).mp heq
    -- `Concrete.DataType.mk.injEq` style — structurally compose.
    cases cdt; cases cdt''
    simp only [Concrete.DataType.mk.injEq]
    exact ⟨hName, hCtors⟩
  -- Step (H): assemble the final .ctor entry into cd.pairs.toList.
  refine ⟨cc, ?_⟩
  rw [hKeyEq]
  rw [hCdEq] at hcd_ctor_get
  exact IndexMap.mem_pairs_of_getByKey _ _ _ hcd_ctor_get

-- `RankTransport` def moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

/-- Structural invariant: every `.dataType` in `cd` is keyed by its own name. -/
@[expose]
def Concrete.Decls.DtNameIsKey (cd : Concrete.Decls) : Prop :=
  ∀ g dt, cd.getByKey g = some (.dataType dt) → g = dt.name

-- MOVED to Scratch.lean (orphan cluster):
--   `DirectDagBody.spine_transfer`, `concretize_preserves_direct_dag`,
--   `sizeBound_ok_strong`, `sizeBound_ok_of_rank`,
--   `concretize_produces_sizeBoundOk`, `concretize_layoutMap_progress`.

-- `Typed.Decls.concretize_progress` DELETED (orphan wrapper over the deleted
-- `concretize_ok_of_invariants`). `Toplevel.compile_progress` uses
-- `WellFormed.monoTerminates` directly.

-- `typFlatSize_eq_typSize_of_concretize` DELETED (orphan speculative infra —
-- no caller). Reintroduce with proper sig when a specific caller needs the
-- source/concrete flat-size equality.

-- `Concrete.Decls.LayoutKeysMatch` and `IndexMap.pairs_toList_keys_unique`
-- moved upstream to `ConcretizeSound/Layout.lean` so that
-- `layoutMap_dataType_size_extract` can take `LayoutKeysMatch` as a hypothesis.

/-- Helper: given `cd.layoutMap = .ok lm`, every `.dataType dt` pair in `cd`
has `lm[dt.name]? = some (.dataType _)`.

**Proof structure**:
1. Unfold `cd.layoutMap` to the fold form over `cd.pairs.toList`.
2. Bridge `hget : cd.getByKey g = some (.dataType dt)` to
   `(g, .dataType dt) ∈ cd.pairs.toList` via `pairsIndexed` + `LawfulBEq`.
3. Induct on the fold suffix with invariant "for every `(g', .dataType dt')`
   in the processed prefix, `acc.1[dt'.name]? = some (.dataType _)`".
4. Step preservation uses 4 distinctness facts assembled inline:
   - `hFnDtName`: a function-insert at `f.name = gF` can't overwrite a prior
     dataType's `dt'.name = gD` entry (IndexMap-uniqueness contradiction).
   - `hDtDtName`: two `.dataType` entries with equal `.name` coincide.
   - `hDtCtorKey`: a prior `.dataType` at `g'` can't be overwritten by a
     constructor-insert at `dt_h.name.pushNamespace c.nameHead` — because
     `hLKM.2.2.2` (ctorPresent) proves an actual `.constructor` entry at
     that key in cd, so a rival `.dataType` at that key contradicts IndexMap
     uniqueness.
   - For the current-step dataType (head case): `Global.ne_pushNamespace` —
     no ctor-insert key equals the inserted dt's own name. -/
theorem layoutMap_getByKey_dt
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hLKM : Concrete.Decls.LayoutKeysMatch cd)
    {g : Global} {dt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType dt)) :
    ∃ n, lm[dt.name]? = some (.dataType n) := by
  -- Unfold layoutMap to fold form.
  have hrw : Concrete.Decls.layoutMap cd = (do
      let r ← cd.pairs.toList.foldlM (layoutMapPass cd)
        (({}, 0) : LayoutMap × Nat)
      pure r.1) := by
    unfold Concrete.Decls.layoutMap
    simp only [IndexMap.foldlM]
    rw [← Array.foldlM_toList]
    rfl
  rw [hrw] at hlm
  -- Extract the inner fold result.
  cases hfold_r : cd.pairs.toList.foldlM (layoutMapPass cd)
                    (({}, 0) : LayoutMap × Nat) with
  | error e => rw [hfold_r] at hlm; simp [bind, Except.bind] at hlm
  | ok res =>
    rw [hfold_r] at hlm
    simp only [bind, Except.bind, pure, Except.pure] at hlm
    -- hlm : res.1 = lm; we prove ∃ n, res.1[dt.name]? = some (.dataType n).
    -- Bridge hget → membership in pairs.toList.
    have hmem : (g, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList := by
      unfold IndexMap.getByKey at hget
      cases hi : cd.indices[g]? with
      | none => rw [hi] at hget; simp at hget
      | some i =>
        rw [hi] at hget
        have hbindform : (some i >>= (cd.pairs[·]?.map Prod.snd))
            = cd.pairs[i]?.map Prod.snd := rfl
        rw [hbindform] at hget
        have hlt : i < cd.pairs.size := (cd.validIndices g hi).1
        have hget? : cd.pairs[i]? = some (cd.pairs[i]'hlt) := by
          rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
        rw [hget?] at hget
        simp only [Option.map_some] at hget
        have hfstBeq : (cd.pairs[i]'hlt).1 == g := (cd.validIndices g hi).2
        have hfstEq : (cd.pairs[i]'hlt).1 = g := LawfulBEq.eq_of_beq hfstBeq
        rw [Array.mem_toList_iff, Array.mem_iff_getElem]
        refine ⟨i, hlt, ?_⟩
        cases hp : cd.pairs[i]'hlt with
        | mk a b =>
          rw [hp] at hfstEq hget
          -- hfstEq : a = g, hget : some (a, b).snd = some (.dataType dt)
          simp only [Option.some.injEq] at hget
          -- hget : (a, b).snd = .dataType dt, i.e. b = .dataType dt
          show (a, b) = (g, Concrete.Declaration.dataType dt)
          subst hfstEq
          exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, hget⟩
    -- Abbreviate cd.pairs.toList as L.
    let L : List (Global × Concrete.Declaration) := cd.pairs.toList
    have hL : L = cd.pairs.toList := rfl
    -- Key fact (for key-uniqueness in L): two pairs with equal first component coincide.
    have hUniqL : ∀ (p1 p2 : Global × Concrete.Declaration),
        p1 ∈ L → p2 ∈ L → p1.1 = p2.1 → p1 = p2 := fun p1 p2 h1 h2 hk =>
      IndexMap.pairs_toList_keys_unique cd p1 p2
        (by rw [hL] at h1; exact h1) (by rw [hL] at h2; exact h2) hk
    -- Dtn=ctor-key distinctness lemma (uses hLKM's ctorPresent conjunct).
    -- If cd has `.dataType dt''` at g'' and `.dataType dt'` at g' (in L), with
    -- `c ∈ dt'.constructors`, then `g'' ≠ dt'.name.pushNamespace c.nameHead`.
    have hDtCtorKey :
      ∀ (g'' g' : Global) (dt'' dt' : Concrete.DataType) (c : Concrete.Constructor),
        (g'', Concrete.Declaration.dataType dt'') ∈ L →
        (g', Concrete.Declaration.dataType dt') ∈ L →
        c ∈ dt'.constructors →
        g'' ≠ dt'.name.pushNamespace c.nameHead := by
      intro g'' g' dt'' dt' c h1 h2 hc
      have hg'eq : cd.getByKey g' = some (.dataType dt') :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h2
      -- Derive ctor-presence in cd.
      obtain ⟨cdt, cc, hctorGet⟩ := hLKM.2.2.2 g' dt' hg'eq c hc
      have hg''eq : cd.getByKey g'' = some (.dataType dt'') :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h1
      intro hkey
      -- Then cd.getByKey g'' = .constructor cdt cc (from hctorGet, rewriting by hkey).
      rw [hkey] at hg''eq
      rw [hctorGet] at hg''eq
      cases hg''eq
    -- Dt-dt name distinctness: two .dataType entries with same dt.name have same pair.
    have hDtDtName :
      ∀ (g₁ g₂ : Global) (dt₁ dt₂ : Concrete.DataType),
        (g₁, Concrete.Declaration.dataType dt₁) ∈ L →
        (g₂, Concrete.Declaration.dataType dt₂) ∈ L →
        dt₁.name = dt₂.name → g₁ = g₂ ∧ dt₁ = dt₂ := by
      intro g₁ g₂ dt₁ dt₂ h1 h2 hname
      have hg1 : cd.getByKey g₁ = some (.dataType dt₁) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h1
      have hg2 : cd.getByKey g₂ = some (.dataType dt₂) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h2
      have hk1 : g₁ = dt₁.name := hLKM.2.1 g₁ dt₁ hg1
      have hk2 : g₂ = dt₂.name := hLKM.2.1 g₂ dt₂ hg2
      have hk : g₁ = g₂ := by rw [hk1, hk2, hname]
      have hpair : (g₁, Concrete.Declaration.dataType dt₁) =
                   (g₂, Concrete.Declaration.dataType dt₂) :=
        hUniqL _ _ h1 h2 hk
      refine ⟨hk, ?_⟩
      have h2nd : Concrete.Declaration.dataType dt₁ = Concrete.Declaration.dataType dt₂ :=
        (Prod.mk.injEq _ _ _ _).mp hpair |>.2
      cases h2nd; rfl
    -- Fn-dt name distinctness: function-entry key ≠ any dataType's dt.name.
    have hFnDtName :
      ∀ (gF gD : Global) (f : Concrete.Function) (dtD : Concrete.DataType),
        (gF, Concrete.Declaration.function f) ∈ L →
        (gD, Concrete.Declaration.dataType dtD) ∈ L →
        f.name ≠ dtD.name := by
      intro gF gD f dtD hF hD heq
      have hgF : cd.getByKey gF = some (.function f) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hF
      have hgD : cd.getByKey gD = some (.dataType dtD) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hD
      have hkF : gF = f.name := hLKM.1 gF f hgF
      have hkD : gD = dtD.name := hLKM.2.1 gD dtD hgD
      have hkFD : gF = gD := by rw [hkF, hkD, heq]
      -- Two pairs at same key with different decls → contradiction.
      have hp := hUniqL _ _ hF hD hkFD
      injection hp with _ hdecl
      cases hdecl
    -- Main fold induction. Target: ∃ n, res.1[dt.name]? = some (.dataType n).
    -- We prove: for any suffix `ys` of L, if fold from init succeeds to `acc`,
    -- and init already satisfies "every seen dt pair has its dt.name entry
    -- populated", and invariant is preserved, then final acc satisfies it on
    -- all pairs in (prefix ++ ys) = L.
    -- Formalize with explicit prefix/suffix decomposition.
    suffices h : ∀ (prefixL ys : List (Global × Concrete.Declaration))
        (init final : LayoutMap × Nat),
      prefixL ++ ys = L →
      (∀ g' dt', (g', Concrete.Declaration.dataType dt') ∈ prefixL →
          ∃ n, init.1[dt'.name]? = some (.dataType n)) →
      ys.foldlM (layoutMapPass cd) init = .ok final →
      ∀ g' dt', (g', Concrete.Declaration.dataType dt') ∈ prefixL ++ ys →
          ∃ n, final.1[dt'.name]? = some (.dataType n) by
      have hall := h [] L ({}, 0) res rfl (by simp) hfold_r
      rw [List.nil_append] at hall
      have hfinal := hall g dt hmem
      -- hlm : Except.ok res.fst = Except.ok lm ⇒ res.fst = lm.
      have hres_eq : res.1 = lm := by
        injection hlm
      rw [hres_eq] at hfinal
      exact hfinal
    intro prefixL ys
    induction ys generalizing prefixL with
    | nil =>
      intro init final _hprefEq hinit hfold
      simp only [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      intro g' dt' hmem'
      rw [List.append_nil] at hmem'
      exact hinit g' dt' hmem'
    | cons head rest ih =>
      intro init final hprefEq hinit hfold
      simp only [List.foldlM_cons, bind, Except.bind] at hfold
      split at hfold
      · cases hfold
      · rename_i acc' hstep
        -- Apply IH with prefix := prefixL ++ [head], ys := rest, init := acc'.
        have hprefEq' : (prefixL ++ [head]) ++ rest = L := by
          rw [List.append_assoc]; exact hprefEq
        intro g' dt' hmemFinal
        -- head ∈ L.
        have hhead_memL : head ∈ L := by
          rw [← hprefEq]
          exact List.mem_append_right _ (List.mem_cons_self)
        -- Key: acc' preserves dataType entries for prefixL pairs + adds head if it's a dataType.
        have hinit' : ∀ g'' dt'',
            (g'', Concrete.Declaration.dataType dt'') ∈ prefixL ++ [head] →
            ∃ n, acc'.1[dt''.name]? = some (.dataType n) := by
          intro g' dt' hmem'
          rw [List.mem_append] at hmem'
          rcases hmem' with hin_pref | hin_head
          · -- In prefixL: preserved by step (we show acc'.1[dt'.name]? = init.1[dt'.name]?).
            obtain ⟨n, hn⟩ := hinit g' dt' hin_pref
            -- Show: step preserves dt'.name lookup when (g', dataType dt') was in prefixL.
            -- For that, need: head's insertion keys ≠ dt'.name.
            -- head.snd is .dataType / .function / .constructor. Case-split.
            -- First, membership of (g', .dataType dt') in L (via prefixL ⊆ L).
            have hmemL : (g', Concrete.Declaration.dataType dt') ∈ L := by
              rw [← hprefEq]; exact List.mem_append_left _ hin_pref
            -- Unfold step on head.
            obtain ⟨headKey, headDecl⟩ := head
            unfold layoutMapPass at hstep
            cases headDecl with
            | constructor _ _ =>
              simp only at hstep
              -- No insert; acc' = init.
              have : acc' = (init.1, init.2) := by
                simp [pure, Except.pure] at hstep
                exact hstep.symm
              rw [this]
              exact ⟨n, hn⟩
            | function f =>
              -- step computes inputSize, outputSize, offsets; inserts at f.name.
              -- Extract the insert: acc'.1 = init.1.insert f.name (.function _).
              simp only [bind, Except.bind] at hstep
              split at hstep
              · cases hstep
              · rename_i _ _
                split at hstep
                · cases hstep
                · split at hstep
                  · cases hstep
                  · -- After three binds, hstep : pure ... = .ok acc'
                    simp only [pure, Except.pure, Except.ok.injEq] at hstep
                    -- hstep : (init.1.insert f.name (.function ...), init.2 + 1) = acc'
                    -- Show acc'.1[dt'.name]? = some (.dataType n).
                    -- Need f.name ≠ dt'.name.
                    have hne : f.name ≠ dt'.name :=
                      hFnDtName headKey g' f dt' hhead_memL hmemL
                    refine ⟨n, ?_⟩
                    rw [← hstep]
                    show (init.1.insert f.name _)[dt'.name]? = some (.dataType n)
                    rw [Std.HashMap.getElem?_insert]
                    have hbeq : (f.name == dt'.name) = false := by simp [hne]
                    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                    exact hn
            | dataType dt_h =>
              -- step: inserts at dt_h.name (.dataType size), then ctor fold inserts at
              -- dt_h.name.pushNamespace c.nameHead for each c ∈ dt_h.constructors.
              simp only [bind, Except.bind] at hstep
              split at hstep
              · cases hstep
              · rename_i dataTypeSize hdtSize
                -- Inner ctor fold.
                split at hstep
                · cases hstep
                · rename_i innerRes hinnerFold
                  simp only [pure, Except.pure, Except.ok.injEq] at hstep
                  -- hstep : (innerRes.1, init.2) = acc'
                  -- Need: acc'.1[dt'.name]? = some (.dataType n).
                  -- acc'.1 = innerRes.1; innerRes derived from inner fold starting at
                  -- (init.1.insert dt_h.name (.dataType dataTypeSize), 0).
                  -- First show: (init.1.insert dt_h.name (.dataType dataTypeSize))[dt'.name]?
                  -- = some (.dataType n) if dt_h.name ≠ dt'.name,
                  -- or = some (.dataType dataTypeSize) if dt_h.name = dt'.name.
                  -- Either way, it's some (.dataType _).
                  -- Then need ctor fold to preserve that (ctor inserts at
                  -- dt_h.name.pushNamespace c.nameHead ≠ dt'.name).
                  -- headKey for .dataType: by hLKM.2.1, headKey = dt_h.name.
                  have hHeadGet : cd.getByKey headKey = some (.dataType dt_h) :=
                    IndexMap.getByKey_of_mem_pairs _ _ _ hhead_memL
                  have hHeadKeyEq : headKey = dt_h.name := hLKM.2.1 headKey dt_h hHeadGet
                  -- Sub-claim: (init.1.insert dt_h.name (.dataType dataTypeSize))[dt'.name]?
                  --         = some (.dataType _)
                  have hAfterDtInsert :
                      ∃ m, (init.1.insert dt_h.name (.dataType dataTypeSize))[dt'.name]?
                            = some (.dataType m) := by
                    by_cases hn_eq : dt_h.name = dt'.name
                    · refine ⟨dataTypeSize, ?_⟩
                      rw [Std.HashMap.getElem?_insert]
                      simp [hn_eq]
                    · refine ⟨n, ?_⟩
                      rw [Std.HashMap.getElem?_insert]
                      have hbeq : (dt_h.name == dt'.name) = false := by simp [hn_eq]
                      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                      exact hn
                  -- Now the ctor fold. For each c ∈ dt_h.constructors, it inserts at
                  -- dt_h.name.pushNamespace c.nameHead. By hDtCtorKey:
                  --   g' ≠ dt_h.name.pushNamespace c.nameHead
                  -- (since (g', .dataType dt') ∈ L, (headKey = dt_h.name, .dataType dt_h) ∈ L).
                  -- Thus ctor inserts don't overwrite dt'.name entry.
                  -- Preservation lemma: list-style invariance.
                  obtain ⟨m, hmInit⟩ := hAfterDtInsert
                  refine ⟨m, ?_⟩
                  rw [← hstep]
                  show innerRes.1[dt'.name]? = some (.dataType m)
                  have hDt'Key : g' = dt'.name := hLKM.2.1 g' dt'
                    (IndexMap.getByKey_of_mem_pairs _ _ _ hmemL)
                  -- g' ≠ dt_h.name.pushNamespace c.nameHead for each c ∈ dt_h.constructors.
                  have hNoOverwrite : ∀ c ∈ dt_h.constructors,
                      dt'.name ≠ dt_h.name.pushNamespace c.nameHead := by
                    intro c hc
                    have := hDtCtorKey g' headKey dt' dt_h c hmemL hhead_memL hc
                    rw [hDt'Key] at this
                    exact this
                  -- Prove: starting from any state whose dt'.name entry is some .dataType _,
                  -- the ctor fold preserves that.
                  have hStrong :
                    ∀ (cs : List Concrete.Constructor) (s0 sf : LayoutMap × Nat),
                      (∀ c ∈ cs, c ∈ dt_h.constructors) →
                      s0.1[dt'.name]? = some (Layout.dataType m) →
                      List.foldlM
                        (fun (state : LayoutMap × Nat)
                             (constructor : Concrete.Constructor) => do
                          let offsets ← constructor.argTypes.foldlM
                              (init := (#[0] : Array Nat))
                              (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                                let typSyze ← typ.size cd
                                pure $ offsets.push
                                  ((offsets[offsets.size - 1]?.getD 0) + typSyze))
                          let decl : Layout :=
                            Layout.constructor
                              { size := dataTypeSize, offsets := offsets,
                                index := state.2 : ConstructorLayout }
                          let name := dt_h.name.pushNamespace constructor.nameHead
                          pure (state.1.insert name decl, state.2 + 1))
                        s0 cs = .ok sf →
                      sf.1[dt'.name]? = some (Layout.dataType m) := by
                    intro cs
                    induction cs with
                    | nil =>
                      intro s0 sf _ hstart hfold0
                      simp only [List.foldlM_nil, pure, Except.pure,
                        Except.ok.injEq] at hfold0
                      subst hfold0; exact hstart
                    | cons c rest ihCs =>
                      intro s0 sf hcMemAll hstart hfold0
                      simp only [List.foldlM_cons, bind, Except.bind] at hfold0
                      -- hfold0 has a nested inner bind for offsets. Split on that.
                      split at hfold0
                      · cases hfold0
                      · rename_i stateAfterC hstateEq
                        -- hstateEq : (let v ← offsets_fold; pure (s0.insert ..., s0.snd+1))
                        --            = .ok stateAfterC
                        -- hfold0 : rest.foldlM ... stateAfterC = .ok sf
                        -- stateAfterC : LayoutMap × Nat is the state after processing c.
                        -- Apply IH to rest from stateAfterC, assuming stateAfterC[dt'.name]? is OK.
                        have hcMem : c ∈ dt_h.constructors :=
                          hcMemAll c List.mem_cons_self
                        have hne : dt'.name ≠ dt_h.name.pushNamespace c.nameHead :=
                          hNoOverwrite c hcMem
                        -- From hstateEq: split on the offsets fold.
                        have hsDt : stateAfterC.1[dt'.name]? = some (Layout.dataType m) := by
                          split at hstateEq
                          · cases hstateEq
                          · rename_i offsArr _hoffs
                            -- hstateEq : pure (s0.insert ..., s0.snd+1) = .ok stateAfterC
                            simp only [pure, Except.pure, Except.ok.injEq] at hstateEq
                            rw [← hstateEq]
                            change (s0.1.insert (dt_h.name.pushNamespace c.nameHead)
                                (Layout.constructor
                                  { size := dataTypeSize, offsets := offsArr,
                                    index := s0.2 }))[dt'.name]?
                              = some (Layout.dataType m)
                            rw [Std.HashMap.getElem?_insert]
                            have hbeq : (dt_h.name.pushNamespace c.nameHead == dt'.name)
                                = false := by simp [Ne.symm hne]
                            simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                            exact hstart
                        exact ihCs _ sf
                          (fun c' hc' => hcMemAll c' (List.mem_cons_of_mem _ hc'))
                          hsDt hfold0
                  -- Apply hStrong with s0 := (init.1.insert dt_h.name (.dataType dataTypeSize), 0).
                  exact hStrong dt_h.constructors _ innerRes
                    (fun _ hc => hc) hmInit hinnerFold
          · -- hin_head : head ∈ [head] → head itself.
            simp only [List.mem_singleton] at hin_head
            -- head = (g', .dataType dt'). So headKey = g', headDecl = .dataType dt'.
            -- Step inserts at dt'.name.
            subst hin_head
            -- Now step is on (g', .dataType dt'). Unfold it.
            unfold layoutMapPass at hstep
            simp only [bind, Except.bind] at hstep
            split at hstep
            · cases hstep
            · rename_i dataTypeSize _hdtSize
              split at hstep
              · cases hstep
              · rename_i innerRes hinnerFold
                simp only [pure, Except.pure, Except.ok.injEq] at hstep
                refine ⟨dataTypeSize, ?_⟩
                rw [← hstep]
                show innerRes.1[dt'.name]? = some (Layout.dataType dataTypeSize)
                -- Inner ctor fold from (init.1.insert dt'.name (.dataType dataTypeSize), 0)
                -- preserves dt'.name entry (ctor inserts at dt'.name.pushNamespace ≠ dt'.name).
                have hNoOv : ∀ c ∈ dt'.constructors,
                    dt'.name ≠ dt'.name.pushNamespace c.nameHead :=
                  fun _ _ => Global.ne_pushNamespace _ _
                have hStrong :
                  ∀ (cs : List Concrete.Constructor) (s0 sf : LayoutMap × Nat),
                    (∀ c ∈ cs, c ∈ dt'.constructors) →
                    s0.1[dt'.name]? = some (Layout.dataType dataTypeSize) →
                    List.foldlM
                      (fun (state : LayoutMap × Nat)
                           (constructor : Concrete.Constructor) => do
                        let offsets ← constructor.argTypes.foldlM
                            (init := (#[0] : Array Nat))
                            (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                              let typSyze ← typ.size cd
                              pure $ offsets.push
                                ((offsets[offsets.size - 1]?.getD 0) + typSyze))
                        let decl : Layout :=
                          Layout.constructor
                            { size := dataTypeSize, offsets := offsets,
                              index := state.2 : ConstructorLayout }
                        let name := dt'.name.pushNamespace constructor.nameHead
                        pure (state.1.insert name decl, state.2 + 1))
                      s0 cs = .ok sf →
                    sf.1[dt'.name]? = some (Layout.dataType dataTypeSize) := by
                  intro cs
                  induction cs with
                  | nil =>
                    intro s0 sf _ hstart hfold0
                    simp only [List.foldlM_nil, pure, Except.pure,
                      Except.ok.injEq] at hfold0
                    subst hfold0; exact hstart
                  | cons c rest ihCs =>
                    intro s0 sf hcMemAll hstart hfold0
                    simp only [List.foldlM_cons, bind, Except.bind] at hfold0
                    split at hfold0
                    · cases hfold0
                    · rename_i stateAfterC hstateEq
                      have hcMem : c ∈ dt'.constructors :=
                        hcMemAll c List.mem_cons_self
                      have hne : dt'.name ≠ dt'.name.pushNamespace c.nameHead :=
                        hNoOv c hcMem
                      have hsDt : stateAfterC.1[dt'.name]?
                          = some (Layout.dataType dataTypeSize) := by
                        split at hstateEq
                        · cases hstateEq
                        · rename_i offsArr _hoffs
                          simp only [pure, Except.pure, Except.ok.injEq] at hstateEq
                          rw [← hstateEq]
                          change (s0.1.insert (dt'.name.pushNamespace c.nameHead)
                              (Layout.constructor
                                { size := dataTypeSize, offsets := offsArr,
                                  index := s0.2 }))[dt'.name]?
                            = some (Layout.dataType dataTypeSize)
                          rw [Std.HashMap.getElem?_insert]
                          have hbeq : (dt'.name.pushNamespace c.nameHead == dt'.name)
                              = false := by simp [Ne.symm hne]
                          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                          exact hstart
                      exact ihCs _ sf
                        (fun c' hc' => hcMemAll c' (List.mem_cons_of_mem _ hc'))
                        hsDt hfold0
                exact hStrong dt'.constructors _ innerRes
                  (fun _ hc => hc)
                  Std.HashMap.getElem?_insert_self
                  hinnerFold
        refine ih _ _ _ hprefEq' hinit' hfold g' dt' ?_
        -- Goal: (g', .dataType dt') ∈ (prefixL ++ [head]) ++ rest
        -- Have: hmemFinal : (g', .dataType dt') ∈ prefixL ++ (head :: rest)
        -- These are syntactically different; convert.
        rw [List.append_assoc, List.singleton_append]
        exact hmemFinal

/-- `typSize lm t` succeeds on every `RefClosed` concrete type under a
sound `layoutMap`. `layoutMap`-level variant of `typSize_ok_of_refClosed`. -/
theorem typSize_ok_of_refClosed_lm
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hLKM : Concrete.Decls.LayoutKeysMatch cd)
    {t : Concrete.Typ}
    (hrc : Concrete.Typ.RefClosed cd t) :
    ∃ n, typSize lm t = .ok n := by
  induction hrc with
  | unit => refine ⟨0, ?_⟩; unfold typSize; rfl
  | field => refine ⟨1, ?_⟩; unfold typSize; rfl
  | pointer _ _ => refine ⟨1, ?_⟩; unfold typSize; rfl
  | function => refine ⟨1, ?_⟩; unfold typSize; rfl
  | @tuple ts hts ih =>
    unfold typSize
    conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
    apply List.foldlM_except_ok'
    intro acc t' ht'
    obtain ⟨m, hm⟩ := ih t' ht'
    exact ⟨acc + m, by simp [hm, bind, Except.bind, pure, Except.pure]⟩
  | @array inner n hinner ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨n * m, ?_⟩
    unfold typSize
    simp only [hm, bind, Except.bind, pure, Except.pure]
  | @ref g hdt =>
    obtain ⟨dt, hgetG⟩ := hdt
    have hgeq : g = dt.name := hdtkey g dt hgetG
    obtain ⟨n, hn⟩ := layoutMap_getByKey_dt hlm hLKM hgetG
    refine ⟨n, ?_⟩
    unfold typSize
    rw [hgeq, hn]
    rfl


-- `concretize_extract_function_at_name` was an orphan,
-- FullyMonomorphic-dependent; no consumer post entry-bridge migration.

/-! ### Orphan-cluster reintegration from `Scratch.lean`.

The cluster `SizeBoundVisInv` / `sizeBound_ok_strong` / `sizeBound_ok_of_rank` /
`spine_transfer` / `concretize_preserves_direct_dag` discharges the
`Concrete.Decls.SizeBoundOk cd` obligation in `CompilerProgress.sizeBoundOk_entry`.

`spine_transfer` and `concretize_preserves_direct_dag` carry sorry'd bodies; their
docstrings document the residual closure path. -/

/-- Vis invariant carried through `sizeBound_ok_strong`: every element of
`vis` that IS a cd-dt key has rank strictly greater than `rank g`. Elements of
`vis` that are NOT cd-dt keys are unconstrained (the visited check only
triggers for cd-dt keys in practice). -/
@[expose]
def SizeBoundVisInv (cd : Concrete.Decls) (rank : Global → Nat) (g : Global)
    (vis : Std.HashSet Global) : Prop :=
  ∀ g'' : Global, vis.contains g'' = true →
    ∀ dt'', cd.getByKey g'' = some (.dataType dt'') → rank g'' > rank g

/-- Strong-induction core lemma: given SpineRefsBelow-form rank + DtNameIsKey +
RefClosed, `DataType.sizeBound` succeeds at every `(bound, vis)` whose cd-dt
members have rank strictly greater than `rank g`. Recursion grows `vis` by
`dt.name = g` while dropping current rank to `rank g' < rank g`; the invariant
is preserved pointwise because new `vis` elements are either old (with rank
> old-rank > new-rank) or `g` (with rank = old-rank > new-rank). -/
theorem sizeBound_ok_strong
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (rank : Global → Nat)
    (hrank : ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t) :
    ∀ (n : Nat) (g : Global) (dt : Concrete.DataType)
      (bound : Nat) (vis : Std.HashSet Global),
      rank g = n →
      cd.getByKey g = some (.dataType dt) →
      SizeBoundVisInv cd rank g vis →
      ∃ m, Concrete.DataType.sizeBound cd bound vis dt = .ok m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g dt bound vis hrankEq hget hvis
    cases bound with
    | zero =>
      refine ⟨1, ?_⟩; unfold Concrete.DataType.sizeBound; rfl
    | succ bound' =>
      -- `¬ vis.contains dt.name`: dt.name = g (DtNameIsKey); if g ∈ vis, the
      -- vis invariant gives `rank g > rank g` via cd.getByKey g = .dataType dt.
      have hdtName : g = dt.name := hdtkey g dt hget
      have hnvis : ¬ vis.contains dt.name = true := by
        intro hc
        rw [← hdtName] at hc
        have : rank g > rank g := hvis g hc dt hget
        exact Nat.lt_irrefl _ this
      unfold Concrete.DataType.sizeBound
      simp only [hnvis, if_false, Bool.false_eq_true]
      simp only [bind, Except.bind, pure, Except.pure]
      -- Typ-level helper: spine-bounded rank → Typ.sizeBound succeeds.
      -- Invariant on `v`: every cd-dt key in v has rank strictly greater than rank g.
      have htypBound : ∀ (b : Nat) (t : Concrete.Typ) (v : Std.HashSet Global),
          Concrete.Typ.RefClosed cd t →
          Concrete.Typ.SpineRefsBelow rank (rank g) t →
          (∀ g'' : Global, v.contains g'' = true →
              ∀ dt'', cd.getByKey g'' = some (.dataType dt'') →
                rank g'' ≥ rank g) →
          ∃ k, Concrete.Typ.sizeBound cd b v t = .ok k := by
        intro b
        induction b with
        | zero =>
          intros; refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
        | succ b' ihb =>
          intro t v hrc_t hspine hv_inv
          cases t with
          | unit =>
            refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | field =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | pointer t' =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | function ins out =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | tuple ts =>
            cases hrc_t; rename_i hrc_ts
            cases hspine; rename_i hsp_ts
            unfold Concrete.Typ.sizeBound
            conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
            simp only [Array.toList_attach, List.attachWith]
            apply List.foldlM_except_ok'
            intro acc t' ht'
            obtain ⟨t'val, ht'mem, ht'eq⟩ := List.mem_pmap.mp ht'
            subst ht'eq
            obtain ⟨m, hm⟩ := ihb t'val v (hrc_ts t'val ht'mem) (hsp_ts t'val ht'mem) hv_inv
            exact ⟨acc + m, by simp [hm, bind, Except.bind, pure, Except.pure]⟩
          | array t' n₁ =>
            cases hrc_t; rename_i hrc_inner
            cases hspine; rename_i hsp_inner
            obtain ⟨m, hm⟩ := ihb t' v hrc_inner hsp_inner hv_inv
            refine ⟨n₁ * m, ?_⟩
            unfold Concrete.Typ.sizeBound
            simp only [hm, bind, Except.bind, pure, Except.pure]
          | ref g'' =>
            cases hrc_t; rename_i hdt'
            obtain ⟨dt', hget'⟩ := hdt'
            cases hspine; rename_i hrank_lt
            -- rank g'' < rank g. Recurse via outer IH at rank g''.
            have hrank_lt_n : rank g'' < n := hrankEq ▸ hrank_lt
            have hvis' : SizeBoundVisInv cd rank g'' v := by
              intro g''' hc dt''' hget'''
              have := hv_inv g''' hc dt''' hget'''  -- rank g''' ≥ rank g
              exact Nat.lt_of_lt_of_le hrank_lt this
            obtain ⟨k, hk⟩ := ih (rank g'') hrank_lt_n g'' dt' b' v rfl hget' hvis'
            refine ⟨k, ?_⟩
            unfold Concrete.Typ.sizeBound
            simp only [hget', hk]
      -- Vis invariant after inserting dt.name = g: every cd-dt key g'' in
      -- (vis.insert dt.name) has rank g'' ≥ rank g.
      have hVisInsert :
          ∀ g'' : Global, (vis.insert dt.name).contains g'' = true →
            ∀ dt'', cd.getByKey g'' = some (.dataType dt'') → rank g'' ≥ rank g := by
        intro g'' hc dt'' hget''
        rw [Std.HashSet.contains_insert] at hc
        rcases Bool.or_eq_true .. |>.mp hc with heq | hin
        · have hname : dt.name = g'' := LawfulBEq.eq_of_beq heq
          rw [← hname, ← hdtName]
          exact Nat.le_refl _
        · exact Nat.le_of_lt (hvis g'' hin dt'' hget'')
      -- mapM over dt.constructors.
      have hMap := @List.mapM_except_ok _ _ _
        (Concrete.Constructor.sizeBound cd bound' (vis.insert dt.name))
        dt.constructors (by
          intro c hc
          unfold Concrete.Constructor.sizeBound
          apply List.foldlM_except_ok'
          intro acc t ht
          have hrc_decl : Concrete.Declaration.RefClosed cd (.dataType dt) :=
            hrc g _ hget
          have hrc_t : Concrete.Typ.RefClosed cd t := hrc_decl c hc t ht
          have hspine : Concrete.Typ.SpineRefsBelow rank (rank g) t :=
            hrank g dt hget c hc t ht
          obtain ⟨k, hk⟩ :=
            htypBound bound' t (vis.insert dt.name) hrc_t hspine hVisInsert
          exact ⟨acc + k, by simp [hk, bind, Except.bind, pure, Except.pure]⟩)
      obtain ⟨sizes, hsizes⟩ := hMap
      refine ⟨sizes.foldl max 0 + 1, ?_⟩
      simp [hsizes]

/-- Size-bound termination from a spine-bounded rank witness + DtNameIsKey.
The entry-point `SizeBoundOk cd` form quantifies over `vis` with full
cd-dt disjointness; that disjointness vacuously satisfies
`SizeBoundVisInv` (no cd-dt keys in vis → the rank-greater hypothesis
is vacuous). -/
theorem sizeBound_ok_of_rank
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (rank : Global → Nat)
    (hrank : ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t) :
    Concrete.Decls.SizeBoundOk cd := by
  intro bound vis dt hex hdisjoint
  obtain ⟨g, hget⟩ := hex
  -- hdisjoint: for all g' dt', cd.getByKey g' = .dataType dt' → ¬ vis.contains dt'.name.
  -- Translate to SizeBoundVisInv: any g'' ∈ vis that IS a cd-dt key contradicts
  -- disjointness (since DtNameIsKey gives dt''.name = g'', and g'' ∈ vis).
  have hVisInv : SizeBoundVisInv cd rank g vis := by
    intro g'' hcontains dt'' hget''
    exfalso
    have hname : g'' = dt''.name := hdtkey g'' dt'' hget''
    have : ¬ vis.contains dt''.name = true := hdisjoint g'' dt'' hget''
    rw [← hname] at this
    exact this hcontains
  exact sizeBound_ok_strong cd hrc hdtkey rank hrank (rank g) g dt bound vis rfl hget hVisInv

/-- `concretize`'s output inherits a rank-based DAG witness from the source.
Composes `DirectDagBody.spine_transfer` (sorry'd, F=1 — backward-trace through
`concretizeBuild`) with `templateOf` machinery. The body discharges the
`_hDrainShape` premise via a sub-sorry tagged
`BLOCKED-spine-transfer-drain-shape`. -/
theorem concretize_preserves_direct_dag
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    -- `AppRefToDt` invariant on every typed-dt argType. Propagated to
    -- `spine_transfer` → `spine_transfer_aux`'s `.app` arm to discharge
    -- `app_target_is_dt_axiom`. Discharged at the consumer
    -- (`sizeBoundOk_entry`) from `WellFormed.bodyAppRefToDt` via the
    -- typed-side lift through `checkAndSimplify`.
    (hAppRefToDt : ∀ g dt, tds.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Typed.Typ.AppRefToDt tds dt.params t) :
    ∃ rank : Global → Nat,
      ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t := by
  obtain ⟨rank_src, hrank_src⟩ := hacyclic
  let origin : Global → Global := DirectDagBody.templateOf tds cd hconc hunique
  let rank_cd : Global → Nat := fun g => rank_src (origin g)
  refine ⟨rank_cd, ?_⟩
  have htransport : DirectDagBody.RankTransport tds cd rank_src rank_cd := by
    intro g templateName templateDt htemplate
    show rank_src (origin g) = rank_src templateName
    have heq : origin g = templateName :=
      DirectDagBody.templateOf_eq_witness hconc hunique htemplate
    rw [heq]
  intro g cdt hget c hc t ht
  obtain ⟨templateDt, htemplate⟩ := DirectDagBody.templateOf_spec hconc hunique hget
  -- Discharge of `_hDrainShape` premise. The shape asks that every
  -- `(templateName', args')` producing a cd-key dt agrees with the canonical
  -- `templateOf` choice on the templateName component. Proof: the hypothesis
  -- `concretizeName templateName' args' = g'` together with the witnessed
  -- existence of a cd-dt at `g'` packages a `TemplateOf tds cd g' templateName'
  -- _` (using `mkDecls`-side typed dt at `templateName'`); but in fact we
  -- can sidestep the `tds` lookup by going directly through
  -- `templateOf_unique` against the canonical `templateOf` choice, since
  -- both come from the same `ConcretizeUniqueNames` envelope.
  have hDrainShape : ∀ g' templateName' args',
       (∃ cdt' : Concrete.DataType, cd.getByKey g' = some (.dataType cdt')) →
       concretizeName templateName' args' = g' →
       templateName' = DirectDagBody.templateOf tds cd hconc hunique g' := by
    intro g' templateName' args' hex hname
    obtain ⟨cdt', hget'⟩ := hex
    -- Canonical template: `templateOf g'` with witness `templateOf_spec`.
    obtain ⟨templateDt', htemplate'⟩ :=
      DirectDagBody.templateOf_spec hconc hunique hget'
    -- htemplate' : TemplateOf tds cd g' (templateOf … g') templateDt'
    -- Apply uniqueness of `concretizeName` pre-images to identify the
    -- candidate `templateName'` with the canonical `templateOf … g'` choice.
    -- Both pairs (templateName', args') and (templateOf …, witnessed args)
    -- map to g' under `concretizeName`.
    obtain ⟨_htdsTemplate, _hexCdt, witArgs, hwitName⟩ := htemplate'
    -- hwitName : concretizeName (templateOf … g') witArgs = g'
    have hnames_eq : concretizeName templateName' args' =
        concretizeName (DirectDagBody.templateOf tds cd hconc hunique g') witArgs := by
      rw [hname, hwitName]
    have hexists : ∃ d, cd.getByKey (concretizeName templateName' args') = some d :=
      ⟨.dataType cdt', by rw [hname]; exact hget'⟩
    exact (hunique hconc templateName' _ args' witArgs hnames_eq hexists).1
  -- rank_cd_def discharge: trivially by definition of rank_cd.
  have rank_cd_def : ∀ g', rank_cd g' =
      rank_src (DirectDagBody.templateOf tds cd hconc hunique g') := fun _ => rfl
  exact DirectDagBody.spine_transfer hconc hunique hrank_src hAppRefToDt htransport
    rank_cd_def hget htemplate hDrainShape c hc t ht

end Aiur

end -- public section
