module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.Phase4
public import Ix.Aiur.Proofs.ConcretizeSound.TypesNotFunction

/-!
`concretizeBuild_preserves_TermRefsDt` (E.5) downstream relocation.

This module owns the typed-side `TermRefsDt` preservation through
`concretizeBuild`'s 3-fold (srcStep + dtStep + fnStep) plus the fold-level
composition into `concretize`'s output. Sits downstream of `Phase4` so the
proof body has access to the kind-preservation helpers
(`concretizeBuild_preserves_{dataType,ctor}_kind_fwd`) and the explicit
`concretizeBuild_at_newDt_ctor_name` family living in `CtorKind.lean` —
which are themselves downstream of the upstream `RefsDt.lean` where
`rewriteTypedTerm_preserves_RefsDt` and the per-step structural pieces
live.

`concretizeBuild_preserves_TermRefsDt` takes the bridge predicate as an
explicit hypothesis, keeping its body trivial
(`rewriteTypedTerm_preserves_RefsDt` per arm). The bridge is discharged
at the consumer site `concretize_preserves_TermRefsDt` using the drain
state's `MonoHasDecl` invariant plus per-arm kind-preservation helpers.

`step4Lower_fold_preserves_TermRefsDt` and `concretize_preserves_TermRefsDt`
relocate alongside their producer to keep the chain co-located.
-/

public section

namespace Aiur

open Source

/-! ### `concretizeBuild` typed-side `TermRefsDt` preservation. -/

/-- `concretizeBuild` lifts typed-side `TermRefsDt` over its 3-fold output,
provided a bridge `_hRefsBridge` mapping every dt-or-ctor key in the source
typed decls to a dt-or-ctor key in the post-fold output via `rewriteGlobal`.

The bridge captures the structural correspondence between source dt/ctor
keys and `concretizeBuild`'s output: identity-arms (`tArgs.isEmpty`,
dt-source, ctor-source-mono-miss) discharge via
`concretizeBuild_preserves_{dataType,ctor}_kind_fwd`; the mono-hit arm
(ctor source, mono lookup hits at the dt template) discharges via
`concretizeBuild_at_newDt_ctor_name` paired with `MonoHasDecl`.

Body is per-arm dispatch on `concretizeBuild_function_origin_with_body`
(`TypesNotFunction.lean:455`) followed by per-body application of
`rewriteTypedTerm_preserves_RefsDt` (`RefsDt.lean:40`) with `_hRefsBridge`
re-packed as the bridge premise.

The bridge is promoted from an internal sub-claim (originally sorried
in the upstream `RefsDt.lean` due to import-order constraints) to an
explicit caller-supplied hypothesis. Both this theorem and its consumer
`concretize_preserves_TermRefsDt` are sorry-free (Arm-C-poly discharged
via `drain_populates_mono_for_body_ref_polymorphic` backed by the
`NewFnBodyRefsCovered` drain invariant). -/
theorem concretizeBuild_preserves_TermRefsDt
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (htdsRef : Typed.Decls.TermRefsDt typedDecls)
    (hnfRef : ∀ f ∈ newFunctions, Typed.Term.RefsDt typedDecls f.body)
    -- The bridge premise takes a body-witness. The witness is satisfied
    -- at the call site in `rewriteTypedTerm_preserves_RefsDt`'s `.ref`
    -- arm by `AppearsAsRef.refSelf` composed (via `hThread`) up to the
    -- outer function-body. The witness discriminates between "source
    -- function body" and "newFunctions body": the consumer
    -- (`concretize_preserves_TermRefsDt`) uses this to dispatch to
    -- `drain_populates_mono_for_body_ref_polymorphic` for Arm-C-poly.
    (_hRefsBridge : ∀ g tArgs,
      ((∃ g_fn f_src, typedDecls.getByKey g_fn = some (.function f_src) ∧
          f_src.params = [] ∧
          Typed.Term.AppearsAsRef g tArgs f_src.body) ∨
       (∃ f ∈ newFunctions,
          Typed.Term.AppearsAsRef g tArgs f.body)) →
      (∃ dt c, typedDecls.getByKey g = some (.constructor dt c) ∧
        (dt.params.isEmpty ∨ ¬ tArgs.isEmpty)) →
      ∃ dt c,
        (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
          (rewriteGlobal typedDecls mono g tArgs) = some (.constructor dt c) ∧
        (dt.params.isEmpty ∨
          ¬ (tArgs.map (rewriteTyp (fun _ => none) mono)).isEmpty)) :
    Typed.Decls.TermRefsDt
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  intro g f_mono hget
  -- Origin-inversion via the body-equation companion lemma in TypesNotFunction.
  rcases concretizeBuild_function_origin_with_body
      typedDecls mono newFunctions newDataTypes hget with
    h_src | h_nf
  · -- Source origin: f_mono.body = rewriteTypedTerm typedDecls emptySubst mono f_src.body.
    obtain ⟨f_src, hsrc_get, hparams, hbody_eq⟩ := h_src
    rw [hbody_eq]
    have hf_src_RefsDt : Typed.Term.RefsDt typedDecls f_src.body :=
      htdsRef g f_src hsrc_get
    exact rewriteTypedTerm_preserves_RefsDt (mono := mono)
      (decls := typedDecls) (body0 := f_src.body) hf_src_RefsDt
      (fun _ _ h => h)
      (fun g' tArgs' hApp hctor =>
        _hRefsBridge g' tArgs'
          (Or.inl ⟨g, f_src, hsrc_get, hparams, hApp⟩) hctor)
  · -- newFunctions origin.
    obtain ⟨f_nf, hf_mem, _hname, hbody_eq⟩ := h_nf
    rw [hbody_eq]
    exact rewriteTypedTerm_preserves_RefsDt (mono := mono)
      (decls := typedDecls) (body0 := f_nf.body) (hnfRef f_nf hf_mem)
      (fun _ _ h => h)
      (fun g' tArgs' hApp hctor =>
        _hRefsBridge g' tArgs'
          (Or.inr ⟨f_nf, hf_mem, hApp⟩) hctor)

/-! ### `step4Lower` fold: typed-side → concrete-side `TermRefsDt`. -/

/-- `step4Lower` fold lifts `Typed.Decls.TermRefsDt monoDecls` to
`Concrete.Decls.TermRefsDt cd` — assembled via `step4Lower_fold_function_origin`
(F=0 in `RefsDt.lean`), `step4Lower_fold_dataType_bridge_inline` /
`step4Lower_fold_ctor_bridge_inline` (F=0 in `Shapes.lean`) for the dt/ctor
bridge, and `termToConcrete_preserves_RefsDt`. Co-located with
`concretizeBuild_preserves_TermRefsDt`. -/
theorem step4Lower_fold_preserves_TermRefsDt
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmdRef : Typed.Decls.TermRefsDt monoDecls)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    Concrete.Decls.TermRefsDt concDecls := by
  intro g cf hcf_get
  -- Step (1): function-origin inversion.
  obtain ⟨f, hmd_get, hbody_eq⟩ :=
    step4Lower_fold_function_origin hcf_get hfold
  -- Step (2): typed-side body has RefsDt monoDecls.
  have hbody_typed : Typed.Term.RefsDt monoDecls f.body := hmdRef g f hmd_get
  -- Step (3): bridge monoDecls dt/ctor keys to concDecls dt/ctor keys.
  have hwit : ∀ g',
      ((∃ dt, monoDecls.getByKey g' = some (.dataType dt)) ∨
       (∃ dt c, monoDecls.getByKey g' = some (.constructor dt c))) →
      ((∃ dt, concDecls.getByKey g' = some (.dataType dt)) ∨
       (∃ dt c, concDecls.getByKey g' = some (.constructor dt c))) := by
    intro g' hmd
    rcases hmd with ⟨dt, hdt⟩ | ⟨dt, c, hctor⟩
    · exact Or.inl (step4Lower_fold_dataType_bridge_inline hdt hfold)
    · exact Or.inr (step4Lower_fold_ctor_bridge_inline hctor hfold)
  -- Step (4): apply termToConcrete_preserves_RefsDt.
  exact termToConcrete_preserves_RefsDt hbody_typed hwit hbody_eq

-- `Typed.Term.AppearsAsRef` was relocated upstream to `RefsDt.lean`
-- so it is in scope at `rewriteTypedTerm_preserves_RefsDt`'s body-witness
-- bridge premise (used to thread Arm-C-poly's drain-reachability discharge).

/-! ### `collectCalls` inserts `(dt.name, tArgs)` for every `.ref` subterm.

Structural induction on `AppearsAsRef body g tArgs`: for every `.ref _ _ g tArgs`
subterm of `body` with `tArgs.nonempty` and `tds.getByKey g = some (.constructor
dt _)`, `(dt.name, tArgs)` is in `collectCalls tds seen body` regardless of the
initial `seen` accumulator. Mirrors `collectCalls_subset` (DrainInvariants.lean
at line 734) but populating `(dt.name, tArgs)` instead of preserving `seen`.

Helper abbreviation: once `(dt.name, tArgs) ∈ acc`, subsequent
`collectCalls tds acc body'` preserves membership. -/
theorem collectCalls_inserts_ref_for_AppearsAsRef
    {tds : Typed.Decls} {body : Typed.Term} {g : Global} {tArgs : Array Typ}
    {dt : DataType} {c : Constructor}
    (h : Typed.Term.AppearsAsRef g tArgs body)
    (hg : tds.getByKey g = some (.constructor dt c))
    (htArgs : ¬ tArgs.isEmpty)
    (seen : Std.HashSet (Global × Array Typ)) :
    (dt.name, tArgs) ∈ collectCalls tds seen body := by
  -- Local helper: if `(dt.name, tArgs) ∈ acc`, subsequent collectCalls preserves.
  have CC_pres : ∀ (body' : Typed.Term)
      (acc : Std.HashSet (Global × Array Typ)),
      (dt.name, tArgs) ∈ acc →
      (dt.name, tArgs) ∈ collectCalls tds acc body' :=
    fun body' acc hmem => collectCalls_subset tds body' acc (dt.name, tArgs) hmem
  -- Preservation of `(dt.name, tArgs) ∈ acc` through `List.foldl collectCalls`
  -- on case-bodies (`bs : List (Pattern × Typed.Term)`, project `.snd`). Used
  -- in the `match`/`appArg` arms.
  have list_pres_pc : ∀ (bs : List (Pattern × Typed.Term))
      (acc : Std.HashSet (Global × Array Typ)),
      (dt.name, tArgs) ∈ acc →
      (dt.name, tArgs) ∈ bs.foldl
        (fun s pb => collectCalls tds s pb.snd) acc := by
    intro bs
    induction bs with
    | nil => intro acc h; exact h
    | cons hd tl ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (CC_pres hd.snd _ h)
  -- Same for `List Typed.Term` args (no `.snd` projection).
  have list_pres_args : ∀ (xs : List Typed.Term)
      (acc : Std.HashSet (Global × Array Typ)),
      (dt.name, tArgs) ∈ acc →
      (dt.name, tArgs) ∈ xs.foldl (collectCalls tds) acc := by
    intro xs
    induction xs with
    | nil => intro acc h; exact h
    | cons hd tl ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (CC_pres hd _ h)
  -- `g`, `tArgs` are PARAMETERS of `AppearsAsRef`, so `induction h` does NOT
  -- generalize hypotheses mentioning them. `hg`, `htArgs` stay in scope at
  -- every arm; the IH for sub-terms is `∀ seen, (dt.name, tArgs) ∈ collectCalls
  -- tds seen sub`. Mechanical recursion structure: each container arm uses
  -- list-foldl preservation (`list_pres_pc` / `list_pres_args`) and the IH at
  -- a specific accumulator; each leaf-binary arm chains via `CC_pres`.
  induction h generalizing seen with
  | @refSelf typ e =>
    unfold collectCalls
    rw [if_neg htArgs, hg]
    exact Std.HashSet.mem_insert_self
  | @tuple typ e ts sub hmem _ ih =>
    unfold collectCalls
    rw [show (ts.attach.foldl (fun s ⟨t, _⟩ => collectCalls tds s t) seen) =
            ts.foldl (collectCalls tds) seen from Array.foldl_attach,
        ← Array.foldl_toList]
    have hmem_list : sub ∈ ts.toList := Array.mem_toList_iff.mpr hmem
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem_list
    rw [hsplit, List.foldl_append, List.foldl_cons]
    exact list_pres_args post _ (ih (pre.foldl (collectCalls tds) seen))
  | @array typ e ts sub hmem _ ih =>
    unfold collectCalls
    rw [show (ts.attach.foldl (fun s ⟨t, _⟩ => collectCalls tds s t) seen) =
            ts.foldl (collectCalls tds) seen from Array.foldl_attach,
        ← Array.foldl_toList]
    have hmem_list : sub ∈ ts.toList := Array.mem_toList_iff.mpr hmem
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem_list
    rw [hsplit, List.foldl_append, List.foldl_cons]
    exact list_pres_args post _ (ih (pre.foldl (collectCalls tds) seen))
  | @ret typ e sub _ ih =>
    unfold collectCalls
    exact ih seen
  | @letV typ e pat v b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @letB typ e pat v b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen v)
  | @matchScrut typ e scrut cases _ ih =>
    unfold collectCalls
    have hscrut : (dt.name, tArgs) ∈ collectCalls tds seen scrut := ih seen
    rw [show (cases.attach.foldl (fun s ⟨(_, b), _⟩ => collectCalls tds s b)
              (collectCalls tds seen scrut)) =
            cases.foldl (fun s pb => collectCalls tds s pb.snd)
              (collectCalls tds seen scrut) from
        List.foldl_attach (l := cases)
          (f := fun s pb => collectCalls tds s pb.snd)
          (b := collectCalls tds seen scrut)]
    exact list_pres_pc cases _ hscrut
  | @matchCase typ e scrut cases pc hmem _ ih =>
    unfold collectCalls
    rw [show (cases.attach.foldl (fun s ⟨(_, b), _⟩ => collectCalls tds s b)
              (collectCalls tds seen scrut)) =
            cases.foldl (fun s pb => collectCalls tds s pb.snd)
              (collectCalls tds seen scrut) from
        List.foldl_attach (l := cases)
          (f := fun s pb => collectCalls tds s pb.snd)
          (b := collectCalls tds seen scrut)]
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
    rw [hsplit, List.foldl_append, List.foldl_cons]
    exact list_pres_pc post _ (ih (pre.foldl
      (fun s pb => collectCalls tds s pb.snd) (collectCalls tds seen scrut)))
  | @appArg typ e g_app tArgs_app args u a hmem _ ih =>
    unfold collectCalls
    rw [show (args.attach.foldl (fun s ⟨a, _⟩ => collectCalls tds s a) seen) =
            args.foldl (collectCalls tds) seen from List.foldl_attach]
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
    have h_pre_post : (dt.name, tArgs) ∈
        (pre ++ a :: post).foldl (collectCalls tds) seen := by
      rw [List.foldl_append, List.foldl_cons]
      exact list_pres_args post _ (ih (pre.foldl (collectCalls tds) seen))
    rw [← hsplit] at h_pre_post
    have h_args_done : (dt.name, tArgs) ∈ args.foldl (collectCalls tds) seen :=
      h_pre_post
    split
    · exact h_args_done
    · split
      · rw [Std.HashSet.mem_insert]; exact Or.inr h_args_done
      · rw [Std.HashSet.mem_insert]; exact Or.inr h_args_done
      · exact h_args_done
  | @addL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @addR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @subL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @subR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @mulL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @mulR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @eqZero typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @proj typ e a n _ ih =>
    unfold collectCalls; exact ih seen
  | @get typ e a n _ ih =>
    unfold collectCalls; exact ih seen
  | @slice typ e a i j _ ih =>
    unfold collectCalls; exact ih seen
  | @setA typ e a n v _ ih =>
    unfold collectCalls
    exact CC_pres v _ (ih seen)
  | @setV typ e a n v _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @store typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @load typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @ptrVal typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @assertEqA typ e a b r _ ih =>
    unfold collectCalls
    exact CC_pres r _ (CC_pres b _ (ih seen))
  | @assertEqB typ e a b r _ ih =>
    unfold collectCalls
    exact CC_pres r _ (ih (collectCalls tds seen a))
  | @assertEqR typ e a b r _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds (collectCalls tds seen a) b)
  | @ioGetInfo typ e k _ ih =>
    unfold collectCalls; exact ih seen
  | @ioSetInfoK typ e k i l r _ ih =>
    unfold collectCalls
    exact CC_pres r _ (CC_pres l _ (CC_pres i _ (ih seen)))
  | @ioSetInfoI typ e k i l r _ ih =>
    unfold collectCalls
    exact CC_pres r _ (CC_pres l _ (ih (collectCalls tds seen k)))
  | @ioSetInfoL typ e k i l r _ ih =>
    unfold collectCalls
    exact CC_pres r _ (ih (collectCalls tds (collectCalls tds seen k) i))
  | @ioSetInfoR typ e k i l r _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds
      (collectCalls tds (collectCalls tds seen k) i) l)
  | @ioRead typ e i n _ ih =>
    unfold collectCalls; exact ih seen
  | @ioWriteD typ e d r _ ih =>
    unfold collectCalls
    exact CC_pres r _ (ih seen)
  | @ioWriteR typ e d r _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen d)
  | @u8Bit typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @u8ShiftL typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @u8ShiftR typ e a _ ih =>
    unfold collectCalls; exact ih seen
  | @u8XorL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u8XorR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @u8AddL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u8AddR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @u8SubL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u8SubR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @u8AndL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u8AndR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @u8OrL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u8OrR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @u8LessThanL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u8LessThanR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @u32LessThanL typ e a b _ ih =>
    unfold collectCalls
    exact CC_pres b _ (ih seen)
  | @u32LessThanR typ e a b _ ih =>
    unfold collectCalls
    exact ih (collectCalls tds seen a)
  | @debugT typ e label tval r _ ih =>
    unfold collectCalls
    have htval : (dt.name, tArgs) ∈ collectCalls tds seen tval := ih seen
    show (dt.name, tArgs) ∈ collectCalls tds (match (some tval : Option Typed.Term) with
      | some t => collectCalls tds seen t | none => seen) r
    exact CC_pres r _ htval
  | @debugR typ e label t r _ ih =>
    unfold collectCalls
    cases t with
    | none =>
      show (dt.name, tArgs) ∈ collectCalls tds seen r
      exact ih seen
    | some tval =>
      show (dt.name, tArgs) ∈ collectCalls tds (collectCalls tds seen tval) r
      exact ih (collectCalls tds seen tval)

/-! ### Drain invariant: every newFn body-ref site is covered by seen ∪ pending.

For every `f ∈ st.newFunctions`, every `.ref _ _ g tArgs` subterm of `f.body`
with `tArgs.nonempty` and `tds[g] = .constructor dt c` has `(dt.name, tArgs)`
in `st.seen ∪ st.pending`. This is preserved by drain:

* Init: vacuous (empty newFunctions).
* `concretizeDrainEntry`'s `.function`-push step: the new `f` has
  `f.body = substInTypedTerm subst f_template.body` and the step
  *immediately* sets `pending'` to include `collectCalls tds _ f.body`,
  which (via `collectCalls_inserts_ref_for_AppearsAsRef`) contains
  `(dt.name, tArgs)`. For pre-existing `f' ∈ state.newFunctions`,
  `state.seen ⊆ state'.seen` and the entry processed gets moved
  (`state.pending → state'.seen`); other pending entries either stay
  in pending or move to seen.
* `concretizeDrainIter`: clears pending, processes batch, accumulates new
  pending. The batch entries land in `state'.seen`. Discovered entries
  in `state'.pending`. So the seen ∪ pending union grows monotonically.
* `concretizeDrain`: chains iters via fuel induction.

At drained, `pending = ∅` (by `concretizeDrain` termination), so the
invariant collapses to `(dt.name, tArgs) ∈ drained.seen`. -/
def DrainState.NewFnBodyRefsCovered (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, ∀ g tArgs (dt : DataType) (c : Constructor),
    Typed.Term.AppearsAsRef g tArgs f.body →
    tds.getByKey g = some (.constructor dt c) →
    ¬ tArgs.isEmpty →
    (dt.name, tArgs) ∈ st.seen ∨ (dt.name, tArgs) ∈ st.pending

/-- Initial drain state satisfies `NewFnBodyRefsCovered` vacuously. -/
theorem DrainState.NewFnBodyRefsCovered.init {tds : Typed.Decls}
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFnBodyRefsCovered tds
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro f hf
  simp only [Array.not_mem_empty] at hf

/-- `concretizeDrainIter` preserves `NewFnBodyRefsCovered`. The iter clears
`state.pending` to `∅` then runs the foldlM over `state.pending.toArray`.
Pre-existing seen survives (`state.seen ⊆ state'.seen`); entries that were
in `state.pending` get processed during the batch and land in `state'.seen`
(via `concretizeDrainEntry_list_foldlM_consumes_batch`); newly-pushed
functions inherit body-ref coverage via the per-step push semantics
(`collectCalls_inserts_ref_for_AppearsAsRef`). -/
theorem concretizeDrainIter_preserves_NewFnBodyRefsCovered
    {tds : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewFnBodyRefsCovered tds)
    (hstep : concretizeDrainIter tds state = .ok state') :
    state'.NewFnBodyRefsCovered tds := by
  -- Use the list-foldlM preservation directly. The pre-state for the foldlM
  -- is `state0 = { state with pending := ∅ }`. For pre-existing
  -- `f ∈ state.newFunctions` with body-ref site whose key was in
  -- `state.pending`, we lose the pending-membership transition during the
  -- clear step — but we recover via batch-consumption at state'.
  --
  -- Direct approach: prove the property on state' from scratch, dispatching
  -- on whether `f` was pre-existing or newly pushed. We reuse the
  -- foldlM lemma by strengthening the predicate parametrically.
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  -- Strengthened invariant: "every body-ref site is in state.seen ∨ state.pending
  -- ∨ acc.seen ∪ acc.pending", which is monotone through the batch.
  let P : DrainState → Prop := fun acc =>
    ∀ f ∈ acc.newFunctions, ∀ g tArgs (dt : DataType) (c : Constructor),
      Typed.Term.AppearsAsRef g tArgs f.body →
      tds.getByKey g = some (.constructor dt c) →
      ¬ tArgs.isEmpty →
      (dt.name, tArgs) ∈ state.seen ∨ (dt.name, tArgs) ∈ state.pending ∨
      (dt.name, tArgs) ∈ acc.seen ∨ (dt.name, tArgs) ∈ acc.pending
  -- P holds at state0 (foldlM init): everything from hinv survives via Or.inl/Or.inr (state.seen / state.pending).
  let state0 : DrainState := { state with pending := ∅ }
  have hP0 : P state0 := by
    intro f hf g tArgs dt c hApp hg hne
    rcases hinv f hf g tArgs dt c hApp hg hne with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  -- P preserved by concretizeDrainEntry: at each step, either the entry was already
  -- in seen (no change), or it was new (insert into seen' + maybe push fn/dt + grow pending').
  -- Pre-existing newFunctions entries: their body-ref witnesses pre-stepwise are still
  -- in (state.seen ∪ state.pending ∪ pre.seen ∪ pre.pending), but the step might
  -- shrink pending (consume entry) and/or grow seen / pending. In all cases monotone:
  -- pre.seen ⊆ post.seen always; pre.pending may shrink but the consumed entry lands in post.seen.
  -- Newly-pushed fn: pending' = collectCalls _ _ f.body, which contains every body-ref site.
  have hP_step : ∀ (s s' : DrainState) (entry : Global × Array Typ),
      P s → concretizeDrainEntry tds s entry = .ok s' → P s' := by
    intro s s' entry hPs hstep
    intro f hf g tArgs dt c hApp hg hne
    -- Run a separate analysis using the structural form of `concretizeDrainEntry`.
    unfold concretizeDrainEntry at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    by_cases hseen : s.seen.contains (entry.1, entry.2)
    · simp [hseen] at hstep; rw [← hstep] at hf ⊢; exact hPs f hf g tArgs dt c hApp hg hne
    · simp [hseen] at hstep
      split at hstep
      · -- Function arm.
        rename_i f_template hf_get
        by_cases hsz : f_template.params.length = entry.2.size
        · simp [hsz] at hstep
          rw [← hstep] at hf ⊢
          rcases Array.mem_push.mp hf with hin | heq
          · -- Pre-existing.
            rcases hPs f hin g tArgs dt c hApp hg hne with h1 | h2 | h3 | h4
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · -- (dt.name, tArgs) ∈ s.seen ⊆ s'.seen.
              right; right; left
              rw [Std.HashSet.mem_insert]; exact Or.inr h3
            · -- (dt.name, tArgs) ∈ s.pending. Two sub-cases.
              by_cases heq_e : (dt.name, tArgs) = (entry.1, entry.2)
              · -- The consumed entry. Now in s'.seen.
                right; right; left
                rw [Std.HashSet.mem_insert]
                exact Or.inl (heq_e ▸ BEq.rfl)
              · -- Still in pending'. Membership preserved through collectInTyp/collectCalls subset.
                right; right; right
                -- Generic Array-foldl preservation through the inputs chain.
                have list_pres_lt : ∀ (xs : List (Local × Typ)) (acc : Std.HashSet _),
                    (dt.name, tArgs) ∈ acc →
                    (dt.name, tArgs) ∈ xs.foldl
                      (fun s lt => collectInTyp s lt.snd) acc := by
                  intro xs
                  induction xs with
                  | nil => intros _ h; exact h
                  | cons hd tl ih =>
                    intro acc h
                    simp only [List.foldl_cons]
                    exact ih _ (collectInTyp_subset hd.snd acc _ h)
                have h1 := collectInTyp_subset
                  (Typ.instantiate (mkParamSubst f_template.params entry.2) f_template.output)
                  s.pending (dt.name, tArgs) h4
                have h2 := list_pres_lt
                  (f_template.inputs.map fun (l, t) =>
                    (l, Typ.instantiate (mkParamSubst f_template.params entry.2) t)) _ h1
                have h3 := collectInTypedTerm_subset
                  (substInTypedTerm (mkParamSubst f_template.params entry.2) f_template.body)
                  _ (dt.name, tArgs) h2
                exact collectCalls_subset tds _ _ (dt.name, tArgs) h3
          · -- Newly-pushed f. f.body ≡ substInTypedTerm subst f_template.body.
            subst heq
            simp only at hApp
            -- pending' = collectCalls tds _ f.body. AppearsAsRef plants entry.
            right; right; right
            exact collectCalls_inserts_ref_for_AppearsAsRef hApp hg hne _
        · simp [hsz] at hstep
      · -- DataType arm.
        rename_i dt_template hdt_get
        by_cases hsz : dt_template.params.length = entry.2.size
        · simp [hsz] at hstep
          rw [← hstep] at hf ⊢
          rcases hPs f hf g tArgs dt c hApp hg hne with h1 | h2 | h3 | h4
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · -- s.seen ⊆ s'.seen.
            right; right; left
            rw [Std.HashSet.mem_insert]; exact Or.inr h3
          · -- s.pending: dispatch on consumed-entry vs not.
            by_cases heq_e : (dt.name, tArgs) = (entry.1, entry.2)
            · right; right; left
              rw [Std.HashSet.mem_insert]
              exact Or.inl (heq_e ▸ BEq.rfl)
            · -- Still in pending'. Membership preserved through the dt's argTypes foldl.
              right; right; right
              -- pending' = newCtors.foldl (fun s c' => c'.argTypes.foldl collectInTyp s) s.pending.
              -- Generic preservation through nested Array foldl.
              have inner_pres : ∀ (xs : List Typ) (acc : Std.HashSet (Global × Array Typ)),
                  (dt.name, tArgs) ∈ acc →
                  (dt.name, tArgs) ∈ xs.foldl collectInTyp acc := by
                intro xs
                induction xs with
                | nil => intros _ h; exact h
                | cons hd tl ih =>
                  intro acc h
                  simp only [List.foldl_cons]
                  exact ih _ (collectInTyp_subset hd acc _ h)
              have outer_pres : ∀ (cs : List Constructor) (acc : Std.HashSet (Global × Array Typ)),
                  (dt.name, tArgs) ∈ acc →
                  (dt.name, tArgs) ∈ cs.foldl
                    (fun s c' => c'.argTypes.foldl collectInTyp s) acc := by
                intro cs
                induction cs with
                | nil => intros _ h; exact h
                | cons hd tl ih =>
                  intro acc h
                  simp only [List.foldl_cons]
                  exact ih _ (inner_pres _ _ h)
              exact outer_pres _ _ h4
        · simp [hsz] at hstep
      · cases hstep
  -- Lift hP_step over the foldlM via list induction.
  have hP_foldlM_lift : ∀ (L : List (Global × Array Typ)) (s0 sN : DrainState),
      P s0 → L.foldlM (concretizeDrainEntry tds) s0 = .ok sN → P sN := by
    intro L
    induction L with
    | nil =>
      intro s0 sN hP0' hfold
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hfold
      rw [← hfold]; exact hP0'
    | cons hd tl ih =>
      intro s0 sN hP0' hfold
      simp only [List.foldlM, bind, Except.bind] at hfold
      split at hfold
      · cases hfold
      · rename_i s'' hs''
        exact ih s'' sN (hP_step s0 s'' hd hP0' hs'') hfold
  have hP_state' : P state' := hP_foldlM_lift state.pending.toArray.toList state0 state' hP0 hstep
  -- Reduce P state' to state'.NewFnBodyRefsCovered tds. The remaining
  -- branches `state.seen` and `state.pending` need to be lifted to state':
  -- * state.seen ⊆ state'.seen via concretizeDrainEntry_list_foldlM_consumes_batch (old).
  -- * state.pending entries land in state'.seen (consumed batch).
  intro f hf g tArgs dt c hApp hg hne
  rcases hP_state' f hf g tArgs dt c hApp hg hne with h1 | h2 | h3 | h4
  · -- state.seen ⊆ state'.seen.
    have ⟨_, hold⟩ := concretizeDrainIter_pending_in_seen
      (state := state) (state' := state') (tds := tds) (by
        unfold concretizeDrainIter
        rw [← Array.foldlM_toList]
        exact hstep)
    exact Or.inl (hold _ h1)
  · -- state.pending entries → state'.seen via consumes_batch.
    have ⟨hpenseen, _⟩ := concretizeDrainIter_pending_in_seen
      (state := state) (state' := state') (tds := tds) (by
        unfold concretizeDrainIter
        rw [← Array.foldlM_toList]
        exact hstep)
    exact Or.inl (hpenseen _ h2)
  · exact Or.inl h3
  · exact Or.inr h4

/-- `concretizeDrain` preserves `NewFnBodyRefsCovered`. Standard fuel
induction over `concretizeDrainIter_preserves_NewFnBodyRefsCovered`. -/
theorem concretize_drain_preserves_NewFnBodyRefsCovered
    {tds : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.NewFnBodyRefsCovered tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.NewFnBodyRefsCovered tds := by
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
        have hinv' : state'.NewFnBodyRefsCovered tds :=
          concretizeDrainIter_preserves_NewFnBodyRefsCovered hinv hstate'
        exact ih state' hinv' hdrain

/-! ### Drain-reachability: poly-ctor body-refs land in `drained.mono`.

Structural drain-reachability lemma needed by `concretize_preserves_TermRefsDt`'s
bridge to discharge `BLOCKED-RefsDt-Bridge-C-mono-miss`. The claim: every
`.ref g tArgs` subterm appearing in either (a) a monomorphic source function
body or (b) a `drained.newFunctions` body, with `tArgs.nonempty` and
`tds.getByKey g = some (.constructor dt c)`, has its `(dt.name, tArgs)`
populated in `drained.mono`.

Closure status:
* Source body case (`f_src.params = []`): closed below. Composes
  `collectCalls_inserts_ref_for_AppearsAsRef` (the structural induction
  over the body) with `concretize_drain_init_pending_in_seen` (seed → seen)
  and `concretize_drain_preserves_SeenSubsetMono` (seen → mono). Per-decl
  preservation through the seed-step's branches via `collectInTyp_subset` /
  `collectInTypedTerm_subset` / `collectCalls_subset`.

* NewFunctions case (`f ∈ drained.newFunctions`): closed via the drain
  invariant `NewFnBodyRefsCovered` (planted above). At drained,
  `pending = ∅`, so the invariant collapses to `(dt.name, tArgs) ∈
  drained.seen`. `SeenSubsetMono` then lifts to mono. -/
theorem drain_populates_mono_for_body_ref_polymorphic
    {tds : Typed.Decls} {drained : DrainState}
    -- Closure note: the body of this lemma needs `Typed.Decls.AllAppRefToDt
    -- tds` (defined in `RefClosed.lean`, downstream of this file) to invoke
    -- `PendingArgsAppRefToDt.init` + drain preservation. Since `RefClosed`
    -- is downstream of this module, the `AllAppRefToDt` premise is not
    -- threaded through this sig; it is derivable from `WellFormed t` at
    -- the consumer site (`compile_correct`) via existing
    -- `*_of_wellFormed` extractors and discharged through the closure
    -- chain when the body is filled in.
    (_hdrain : concretizeDrain tds (concretizeDrainFuel tds)
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained)
    -- Body-source disjunction: either the body is a monomorphic source
    -- function's body (with `f_src.params = []`) or it is one of
    -- `drained.newFunctions`'s body. In both cases, `concretizeSeed`/
    -- `concretizeDrainEntry`'s `collectCalls` has visited the body's
    -- `.ref _ _ g tArgs` subterms, planting `(dt.name, tArgs) ∈ pending`
    -- whenever `tArgs.nonempty` and `tds.getByKey g = some (.constructor dt _)`.
    -- Drain then converts every reachable `pending` element into `mono`
    -- (via `SeenSubsetMono`).
    (g : Global) (tArgs : Array Typ) (dt : DataType) (c : Constructor)
    (_hg : tds.getByKey g = some (.constructor dt c))
    (_htArgs : ¬ tArgs.isEmpty)
    (_hpoly : ¬ dt.params.isEmpty)
    -- Body witness: there exists either a monomorphic source function body
    -- or a newFunctions body in which `(g, tArgs)` appears as a `.ref` site.
    -- The `Typed.Term.AppearsAsRef body g tArgs` predicate (above) captures
    -- the "appears as `.ref` subterm" relation structurally.
    (_hBodyWitness :
      (∃ g_fn f_src, tds.getByKey g_fn = some (.function f_src) ∧
         f_src.params = [] ∧
         Typed.Term.AppearsAsRef g tArgs f_src.body) ∨
      (∃ f ∈ drained.newFunctions,
         Typed.Term.AppearsAsRef g tArgs f.body)) :
    drained.mono.contains (dt.name, tArgs) := by
  -- Closure plan:
  -- (A) Show `(dt.name, tArgs) ∈ concretizeSeed tds` (source-body witness)
  --     OR `(dt.name, tArgs)` arrives in pending during drain
  --     (newFunctions-body witness).
  -- (B) For both, derive `(dt.name, tArgs) ∈ drained.seen` via
  --     `concretize_drain_init_pending_in_seen` (source) or drain-time
  --     pending discovery (newFunctions).
  -- (C) Apply `SeenSubsetMono` (via `concretize_drain_preserves_SeenSubsetMono`)
  --     to lift `drained.seen` membership to `drained.mono[(g, args)]?.isSome`.
  -- (D) Convert `.isSome` to `.contains` via standard HashMap lemma.
  --
  -- Drain invariants used: `SeenSubsetMono` (preserves through drain) +
  -- `concretize_drain_init_pending_in_seen` (init pending → seen) +
  -- `concretize_drain_seen_subset` (seen monotonicity).
  rcases _hBodyWitness with ⟨g_fn, f_src, hf_get, hp_empty, hAppears⟩ |
                            ⟨f, hf_mem, hAppears⟩
  · -- Source-body case: show `(dt.name, tArgs) ∈ concretizeSeed tds`.
    -- `concretizeSeed` folds over `tds.pairs`; at the `(g_fn, .function f_src)`
    -- entry with `f_src.params.isEmpty`, the inner branch calls
    -- `collectCalls tds <prior-acc> f_src.body`. Our helper
    -- `collectCalls_inserts_ref_for_AppearsAsRef` gives membership under that
    -- collectCalls. Subsequent fold steps preserve via
    -- `collectInTyp_subset` / `collectInTypedTerm_subset` / `collectCalls_subset`.
    have hseed_mem : (dt.name, tArgs) ∈ concretizeSeed tds := by
      -- Step 1: factor out the per-decl seed-step (the lambda body of the
      -- outer fold) and prove it preserves accumulator membership.
      let seedStep : Std.HashSet (Global × Array Typ) → (Global × Typed.Declaration) →
          Std.HashSet (Global × Array Typ) :=
        fun pending p =>
          match p.snd with
          | .function f => if f.params.isEmpty then
              let p1 := collectInTyp pending f.output
              let p2 := f.inputs.foldl (fun s lt => collectInTyp s lt.snd) p1
              let p3 := collectInTypedTerm p2 f.body
              collectCalls tds p3 f.body
            else pending
          | .dataType dt' => if dt'.params.isEmpty then
              dt'.constructors.foldl (fun s c =>
                c.argTypes.foldl collectInTyp s) pending
            else pending
          | _ => pending
      -- Auxiliary: list-fold preservation through `seedStep`.
      have list_pres_typ : ∀ (xs : List Typ) (acc : Std.HashSet _),
          (dt.name, tArgs) ∈ acc →
          (dt.name, tArgs) ∈ xs.foldl collectInTyp acc := by
        intro xs
        induction xs with
        | nil => intros _ h; exact h
        | cons hd tl ih =>
          intro acc h
          simp only [List.foldl_cons]
          exact ih _ (collectInTyp_subset hd acc _ h)
      have list_pres_lt : ∀ (xs : List (Local × Typ)) (acc : Std.HashSet _),
          (dt.name, tArgs) ∈ acc →
          (dt.name, tArgs) ∈ xs.foldl
            (fun s lt => collectInTyp s lt.snd) acc := by
        intro xs
        induction xs with
        | nil => intros _ h; exact h
        | cons hd tl ih =>
          intro acc h
          simp only [List.foldl_cons]
          exact ih _ (collectInTyp_subset hd.snd acc _ h)
      have list_pres_ctor_args : ∀ (cs : List Constructor) (acc : Std.HashSet _),
          (dt.name, tArgs) ∈ acc →
          (dt.name, tArgs) ∈ cs.foldl
            (fun s c => c.argTypes.foldl collectInTyp s) acc := by
        intro cs
        induction cs with
        | nil => intros _ h; exact h
        | cons hd tl ih =>
          intro acc h
          simp only [List.foldl_cons]
          exact ih _ (list_pres_typ hd.argTypes acc h)
      have seedStep_pres : ∀ (acc : Std.HashSet _) (p : Global × Typed.Declaration),
          (dt.name, tArgs) ∈ acc → (dt.name, tArgs) ∈ seedStep acc p := by
        intro acc p h
        simp only [seedStep]
        match hp : p.snd with
        | .function f =>
          by_cases hp2 : f.params.isEmpty
          · simp only [hp2, if_true]
            have h1 := collectInTyp_subset f.output acc _ h
            have h2 := list_pres_lt f.inputs _ h1
            have h3 := collectInTypedTerm_subset f.body _ _ h2
            exact collectCalls_subset tds f.body _ _ h3
          · simp only [hp2]; exact h
        | .dataType dt' =>
          by_cases hp2 : dt'.params.isEmpty
          · simp only [hp2, if_true]
            exact list_pres_ctor_args dt'.constructors _ h
          · simp only [hp2]; exact h
        | .constructor _ _ => exact h
      have list_pres_seed : ∀ (xs : List (Global × Typed.Declaration))
          (acc : Std.HashSet _),
          (dt.name, tArgs) ∈ acc →
          (dt.name, tArgs) ∈ xs.foldl seedStep acc := by
        intro xs
        induction xs with
        | nil => intros _ h; exact h
        | cons hd tl ih =>
          intro acc h
          simp only [List.foldl_cons]
          exact ih _ (seedStep_pres acc hd h)
      -- Step 2: at (g_fn, .function f_src) step, the helper plants membership.
      have hf_pair : (g_fn, Typed.Declaration.function f_src) ∈ tds.pairs.toList :=
        IndexMap.mem_pairs_of_getByKey tds g_fn _ hf_get
      obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf_pair
      have hp_empty_bool : f_src.params.isEmpty = true := List.isEmpty_iff.mpr hp_empty
      -- Compute membership at the (g_fn, .function f_src) step itself.
      have h_step : (dt.name, tArgs) ∈ seedStep (pre.foldl seedStep ∅)
          (g_fn, Typed.Declaration.function f_src) := by
        simp only [seedStep, hp_empty_bool, if_true]
        exact collectCalls_inserts_ref_for_AppearsAsRef hAppears _hg _htArgs _
      -- Step 3: combine via list_pres_seed on post.
      show (dt.name, tArgs) ∈ tds.pairs.foldl seedStep ∅
      rw [← Array.foldl_toList, hsplit, List.foldl_append, List.foldl_cons]
      exact list_pres_seed post _ h_step
    -- (B) Lift seed → drained.seen.
    have hin_seen : (dt.name, tArgs) ∈ drained.seen :=
      concretize_drain_init_pending_in_seen _ _ _hdrain (dt.name, tArgs) hseed_mem
    -- (C) Apply SeenSubsetMono.
    have hSSM : drained.SeenSubsetMono :=
      concretize_drain_preserves_SeenSubsetMono _ _
        (DrainState.SeenSubsetMono.init _) _hdrain
    have hmono_isSome :
        drained.mono[(dt.name, tArgs)]? = some (concretizeName dt.name tArgs) :=
      hSSM dt.name tArgs hin_seen
    -- (D) Convert isSome to contains.
    rw [Std.HashMap.contains_eq_isSome_getElem?, hmono_isSome]
    rfl
  · -- NewFunctions case: `f ∈ drained.newFunctions`.
    -- Apply `concretize_drain_preserves_NewFnBodyRefsCovered` with the
    -- vacuous initial invariant; at `drained`, `pending = ∅` (drain
    -- termination), so the invariant `(dt.name, tArgs) ∈ st.seen ∨
    -- (dt.name, tArgs) ∈ st.pending` collapses to the seen disjunct.
    -- `SeenSubsetMono` lifts seen → mono.
    have hCov : drained.NewFnBodyRefsCovered tds :=
      concretize_drain_preserves_NewFnBodyRefsCovered _ _
        (DrainState.NewFnBodyRefsCovered.init _) _hdrain
    have hPenEmpty : drained.pending.isEmpty :=
      concretize_drain_succeeds_pending_empty _ _ _hdrain
    -- Apply hCov to the AppearsAsRef witness; pending case is vacuous via hPenEmpty.
    rcases hCov f hf_mem g tArgs dt c hAppears _hg _htArgs with hin_seen | hin_pen
    · -- (dt.name, tArgs) ∈ drained.seen: lift to mono via SeenSubsetMono.
      have hSSM : drained.SeenSubsetMono :=
        concretize_drain_preserves_SeenSubsetMono _ _
          (DrainState.SeenSubsetMono.init _) _hdrain
      have hmono_isSome :
          drained.mono[(dt.name, tArgs)]? = some (concretizeName dt.name tArgs) :=
        hSSM dt.name tArgs hin_seen
      rw [Std.HashMap.contains_eq_isSome_getElem?, hmono_isSome]
      rfl
    · -- (dt.name, tArgs) ∈ drained.pending: vacuous since drained.pending = ∅.
      exfalso
      have hcontains : drained.pending.contains (dt.name, tArgs) :=
        Std.HashSet.contains_iff_mem.mpr hin_pen
      rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true.mpr
        ⟨_, hcontains⟩] at hPenEmpty
      cases hPenEmpty

/-! ### Top-level: `concretize` preserves `TermRefsDt` from typed to concrete. -/

/-- **`concretize` lifts `TermRefsDt` from typed to concrete.**

Under `NoTermRefsToFunctions t` (every `.ref g` subterm in source bodies
is keyed to a dt/ctor in `tds`), the concrete `cd` has the same property:
every concrete function body in `cd` has all `.ref g'` subterms keyed to a
dt/ctor in `cd`.

Composition path:
1. **Drain invariant** (F=0): `NewFunctionsTermRefsDt` survives the worklist
   drain — closed via `concretize_drain_preserves_NewFunctionsTermRefsDt`
   (`RefsDt.lean`).
2. **`concretizeBuild` preservation** (F=0 with bridge): typed-side
   `TermRefsDt` survives the 3-fold over `monoDecls`, given the bridge
   `_hRefsBridge` discharged at this site (BLOCKED-RefsDt-Bridge).
3. **`step4Lower` fold preservation** (F=0): `Typed.Decls.TermRefsDt
   monoDecls → Concrete.Decls.TermRefsDt concDecls`.

The bridge discharge (Step 2's hypothesis) requires per-arm reasoning:
* identity arms (`tArgs.isEmpty` / dt-source / ctor-source-mono-miss):
  closed via `concretizeBuild_preserves_{dataType,ctor}_kind_fwd`;
* mono-hit arm (ctor source, mono lookup hits at `(dt.name, tArgs)`):
  closed via `concretizeBuild_at_newDt_ctor_name` paired with
  `MonoHasDecl drained`.

The polymorphic-source case (a `.ref g _ tArgs` whose `g` is a polymorphic
ctor with mono miss, or a polymorphic dt referenced bare) is structurally
unreachable under well-formed Aiur — `refLookup` (`Check.lean:421`) only
produces `.ref` for nullary ctors, and `tArgs` is always pinned to
`dt.params.length` at the type-checker. The corresponding mono lookup is
populated by the drain process whenever the ctor reaches a body
(BodyAppRefToDt + drain reachability). The bridge's full discharge at
this site is sorry-free, via Arm-C-poly drain-reachability discharge
backed by `drain_populates_mono_for_body_ref_polymorphic` (closed with
the `NewFnBodyRefsCovered` drain invariant for the newFunctions case).

Relocated from `Shapes.lean` to co-locate with
`concretizeBuild_preserves_TermRefsDt` (which moved here too due to
needing CtorKind/Phase4 infra). -/
theorem concretize_preserves_TermRefsDt
    {t : Source.Toplevel} {decls : Source.Decls}
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hsrc : NoTermRefsToFunctions t)
    (hUnique : Typed.Decls.ConcretizeUniqueNames tds)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.TermRefsDt cd := by
  -- Reduce `NoTermRefsToFunctions t` + `hts` to typed-side `TermRefsDt tds`.
  have htdsRef : Typed.Decls.TermRefsDt tds := hsrc tds hts
  -- Unpack `concretize` into its 3 stages.
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · rename_i err _ ; cases hconc
  rename_i drained hdrain
  -- Stage 2: drain produces newFunctions all of which satisfy `Typed.Term.RefsDt tds`.
  have hinit : DrainState.NewFunctionsTermRefsDt tds
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } :=
    DrainState.NewFunctionsTermRefsDt.init _
  have hnfRef : ∀ f ∈ drained.newFunctions, Typed.Term.RefsDt tds f.body :=
    concretize_drain_preserves_NewFunctionsTermRefsDt htdsRef
      _ _ hinit hdrain
  -- Drain invariants used in the bridge body below.
  have hSNN : drained.StrongNewNameShape tds :=
    concretize_drain_preserves_StrongNewNameShape _ _
      (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
  have hMHD : drained.MonoHasDecl :=
    concretize_drain_mono_has_decl _ _
      (DrainState.MonoHasDecl.init (concretizeSeed tds)) hdrain
  have hMSO : drained.MonoShapeOk tds :=
    concretize_drain_shape_equation _ _
      (DrainState.MonoShapeOk.init tds (concretizeSeed tds)) hdrain
  -- FnMatchP for source ↔ typed companion lookups.
  have hFnMatchP := FnMatchP_checkAndSimplify hdecls hts
  -- TdDtParamsMatchP gives `tds[g] = some (.dataType dt) → decls[g] = some (.dataType dt)`
  -- with the SAME `dt` value. Used by Arm A / Arm D disjointness arguments to
  -- collapse typed-side `dt_orig` witnesses to source-side `dt` companions.
  have hTdDt := TdDtParamsMatchP_checkAndSimplify hdecls hts
  -- Reconstruct the original `tds.concretize = .ok cd` (pre-`unfold`) so we can
  -- apply `hUnique hconc_orig` for cd-key existence claims inside the bridge.
  have hconc_orig : tds.concretize = .ok cd := by
    unfold Typed.Decls.concretize
    simp only [bind, Except.bind, hdrain]
    exact hconc
  -- Step 4 key-preservation: monoDecls.containsKey g ↔ cd.containsKey g.
  -- Used to lift "g exists in monoDecls" to "g exists in cd" for `hUnique` premises.
  have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hconc
  -- Stage 3 (concretizeBuild): typed-side TermRefsDt on the resulting monoDecls.
  -- `Typed.Term.RefsDt`'s `.ref` arm carries a structural disjunct
  -- `dt.params.isEmpty ∨ ¬ tArgs.isEmpty` (refLookup at Check.lean:421
  -- emits `.ref g #[]` only for mono ctors and `.ref g mvars` with
  -- `mvars.size = dt.params.length > 0` for poly ctors). The bridge
  -- premise here threads the disjunct through: input includes the
  -- disjunct, output produces it post-rewrite. With this shape, Arm
  -- A.ctor can extract `dt.params = []` from the input and apply
  -- `concretizeBuild_preserves_ctor_kind_fwd` directly.
  have hRefsBridge : ∀ g tArgs,
      ((∃ g_fn f_src, tds.getByKey g_fn = some (.function f_src) ∧
          f_src.params = [] ∧
          Typed.Term.AppearsAsRef g tArgs f_src.body) ∨
       (∃ f ∈ drained.newFunctions,
          Typed.Term.AppearsAsRef g tArgs f.body)) →
      (∃ dt c, tds.getByKey g = some (.constructor dt c) ∧
        (dt.params.isEmpty ∨ ¬ tArgs.isEmpty)) →
      ∃ dt c,
        (concretizeBuild tds drained.mono drained.newFunctions
          drained.newDataTypes).getByKey
          (rewriteGlobal tds drained.mono g tArgs) = some (.constructor dt c) ∧
        (dt.params.isEmpty ∨
          ¬ (tArgs.map (rewriteTyp (fun _ => none) drained.mono)).isEmpty) := by
    -- 4-arm dispatch on `rewriteGlobal`:
    --
    --  • Arm A (tArgs.isEmpty + tds[g] = .ctor): rewriteGlobal returns `g`.
    --    With the new disjunct (`dt.params.isEmpty ∨ ¬ tArgs.isEmpty`) and
    --    `tArgs.isEmpty`, the disjunct collapses to `dt.params.isEmpty`. We
    --    apply `PhaseA2.concretizeBuild_preserves_ctor_kind_fwd` modulo the
    --    StrongNewNameShape disjointness premise (the only remaining blocker
    --    here, BLOCKED-RefsDt-Bridge-A-disjoint).
    --  • Arm B (tArgs.nonempty + tds[g] = .ctor + popNamespace = none):
    --    UNREACHABLE per `mkDecls_source_ctor_is_key`. CLOSED.
    --  • Arm C (tArgs.nonempty + tds[g] = .ctor + popNamespace = some +
    --    mono-miss): rewriteGlobal returns `g` (poly ctor key) NOT in
    --    monoDecls. BLOCKED-RefsDt-Bridge-C-mono-miss (drain-reachability).
    --  • Arm D (tArgs.nonempty + tds[g] = .ctor + popNamespace = some +
    --    mono-hit): rewriteGlobal returns `concDTName.pushNamespace ctorName`.
    --    Closed via `concretizeBuild_at_newDt_ctor_name` + MonoShapeOk +
    --    FnMatchP + mkDecls_source_ctor_is_key. Disjointness
    --    BLOCKED-RefsDt-Bridge-D-disjoint (needs ConcretizeUniqueNames).
    intro g tArgs hBodyWitness ⟨dt, c, htd_c, hdisj⟩
    -- Step 0 (universal): source ctor + mkDecls ctor key shape.
    have hsrc_ctor : decls.getByKey g = some (.constructor dt c) :=
      (hFnMatchP g).2.2 dt c htd_c
    have hkey_eq : g = dt.name.pushNamespace c.nameHead :=
      mkDecls_source_ctor_is_key hdecls g dt c hsrc_ctor
    -- Helper: `tArgs.size` matches between original and rewritten Arrays,
    -- so `.isEmpty` transports verbatim.
    have htArgs_isEmpty_iff :
        (tArgs.map (rewriteTyp (fun _ => none) drained.mono)).isEmpty
          = tArgs.isEmpty := by
      have hsize : (tArgs.map (rewriteTyp (fun _ => none) drained.mono)).size
          = tArgs.size := Array.size_map ..
      simp only [Array.isEmpty]
      rw [hsize]
    by_cases htArgs : tArgs.isEmpty
    · -- Arm A (tArgs.isEmpty): rewriteGlobal returns `g`. Disjunct collapses.
      have hrwg_eq : rewriteGlobal tds drained.mono g tArgs = g := by
        unfold rewriteGlobal; simp [htArgs]
      rw [hrwg_eq]
      -- From `tArgs.isEmpty` and the disjunct
      -- `dt.params.isEmpty ∨ ¬ tArgs.isEmpty`, extract
      -- `dt.params.isEmpty`. This is the analytical content:
      -- `refLookup` (Check.lean:421-441) emits `.ref g #[]` only when
      -- `dt.params.isEmpty`.
      have hparams_empty : dt.params.isEmpty := by
        rcases hdisj with h | h
        · exact h
        · exfalso; exact h htArgs
      have hparams_eq : dt.params = [] := List.isEmpty_iff.mp hparams_empty
      -- Express the source ctor key `g = dt.name.pushNamespace c.nameHead` as
      -- `concretizeName dt.name #[.ref ⟨.mkSimple c.nameHead⟩]` (single-limb form)
      -- — the canonical shape that `hUnique` consumes. Pattern from
      -- `SizeBound.lean:1715-1820`.
      let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
      have hg_concName_eq : g = concretizeName dt.name #[collisionArg] := by
        rw [RefClosedBody.concretizeName_singleton_ref_simple, hkey_eq]
      -- The source ctor key `g` is in `tds` as `.constructor _ _` with
      -- `dt.params = []`, so `srcStep` inserts at `g` and subsequent
      -- dtStep/fnStep folds preserve `containsKey g`. Lift to `cd` via
      -- `concretize_step_4_keys_of_fold` for `hUnique` discharge.
      obtain ⟨_, _, hsrc_get_g⟩ :=
        PhaseA2.fromSource_inserts_ctor_at_key tds drained.mono htd_c hparams_eq
      have hsrc_contains_g : (tds.pairs.foldl
          (PhaseA2.srcStep tds drained.mono) default).containsKey g :=
        (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hsrc_get_g]; rfl)
      have hmono_contains_g : (concretizeBuild tds drained.mono drained.newFunctions
          drained.newDataTypes).containsKey g := by
        rw [PhaseA2.concretizeBuild_eq]
        apply PhaseA2.fnStep_foldl_preserves_containsKey
        apply PhaseA2.dtStep_foldl_preserves_containsKey
        exact hsrc_contains_g
      have hcd_contains_g : cd.containsKey g := (hkeys g).mp hmono_contains_g
      have hg_in_cd : ∃ d, cd.getByKey g = some d := by
        rcases h : cd.getByKey g with _ | d
        · exact absurd ((IndexMap.getByKey_isSome_iff_containsKey _ _).mpr
            hcd_contains_g) (by rw [h]; intro h'; cases h')
        · exact ⟨d, rfl⟩
      -- `hDtNotKey` (Arm A): if `dt'.name = g`, hSNN.2 gives `dt'.name = concretizeName g_d args_d`
      -- with `tds[g_d] = .dataType dt_orig` and `args_d.size = dt_orig.params.length`.
      -- Express g as `concretizeName dt.name #[collisionArg]` (single-limb).
      -- Apply `hUnique hconc_orig` to get `g_d = dt.name ∧ args_d = #[collisionArg]`.
      -- Then `tds[g_d] = .dataType dt_orig` lifts to `decls[g_d] = .dataType dt_orig`
      -- via `TdDtParamsMatchP`. With `g_d = dt.name`, `decls[dt.name] = .dataType dt_orig`,
      -- but `decls[dt.name] = .dataType dt` (from mkDecls_ctor_companion + dt.params = []),
      -- so `dt_orig = dt`, hence `dt_orig.params = []`. But `args_d.size = 1` from
      -- `args_d = #[collisionArg]`, contradicting `args_d.size = dt_orig.params.length = 0`.
      have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
        intro dt' hdt'_mem heq
        obtain ⟨g_d, args_d, dt_orig, hd_name, hd_get, hd_sz, _⟩ := hSNN.2 dt' hdt'_mem
        have heq_concName :
            concretizeName g_d args_d = concretizeName dt.name #[collisionArg] := by
          rw [← hd_name, heq, hg_concName_eq]
        have hCdKey : ∃ d, cd.getByKey (concretizeName g_d args_d) = some d := by
          rw [heq_concName, ← hg_concName_eq]; exact hg_in_cd
        obtain ⟨hg_eq, hargs_eq⟩ :=
          hUnique hconc_orig g_d dt.name args_d #[collisionArg] heq_concName hCdKey
        -- Source-side dt-companion at `dt.name`.
        obtain ⟨_hsrc_dt, _⟩ := mkDecls_ctor_companion hdecls g dt c hsrc_ctor
        -- Lift `tds[g_d] = .dataType dt_orig` to `decls[g_d] = .dataType dt_orig`.
        have hd_get_decls : decls.getByKey g_d = some (.dataType dt_orig) :=
          hTdDt g_d dt_orig hd_get
        rw [hg_eq] at hd_get_decls
        rw [_hsrc_dt] at hd_get_decls
        simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hd_get_decls
        -- Now `dt = dt_orig`, hence `dt_orig.params = dt.params = []`.
        have hd_orig_params : dt_orig.params = [] := by
          rw [← hd_get_decls]; exact hparams_eq
        have hsz_zero : args_d.size = 0 := by
          rw [hd_sz, hd_orig_params]; rfl
        have hsz_one : args_d.size = 1 := by
          rw [hargs_eq]; rfl
        omega
      -- `hFnNotKey` (Arm A): if `f.name = g`, hSNN.1 gives `f.name = concretizeName g_f args_f`
      -- with `tds[g_f] = .function f_orig`. Same equation reasoning yields `g_f = dt.name`.
      -- But `decls[dt.name] = .dataType dt` and FnMatchP/TdDtParamsMatchP would force
      -- `tds[dt.name] = .dataType _`, contradicting `.function`.
      have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
        intro f hf heq
        obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
        have heq_concName :
            concretizeName g_f args_f = concretizeName dt.name #[collisionArg] := by
          rw [← hf_name, heq, hg_concName_eq]
        have hCdKey : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
          rw [heq_concName, ← hg_concName_eq]; exact hg_in_cd
        obtain ⟨hg_eq, _hargs_eq⟩ :=
          hUnique hconc_orig g_f dt.name args_f #[collisionArg] heq_concName hCdKey
        -- `tds[g_f] = .function f_orig` and `tds[dt.name]` would have to be a `.dataType`.
        obtain ⟨_hsrc_dt, _⟩ := mkDecls_ctor_companion hdecls g dt c hsrc_ctor
        obtain ⟨td_dt', htd_dt'⟩ := checkAndSimplify_src_dt_to_td hdecls hts _hsrc_dt
        rw [hg_eq] at hf_get
        rw [hf_get] at htd_dt'
        cases htd_dt'
      -- Apply kind-fwd with the extracted `dt.params = []`.
      obtain ⟨md_dt, md_c, hget_md⟩ :=
        PhaseA2.concretizeBuild_preserves_ctor_kind_fwd tds drained.mono
          drained.newFunctions drained.newDataTypes htd_c hparams_eq
          hDtNotKey hFnNotKey
      refine ⟨md_dt, md_c, hget_md, ?_⟩
      -- Need `md_dt.params.isEmpty` to discharge the output disjunct. Trace
      -- through concretizeBuild's 3-fold:
      --
      -- (a) `fromSource_inserts_ctor_at_key_explicit` gives the srcStep value
      --     at g as `.constructor { dt with constructors := rwCtors } newCtor`,
      --     so srcStep-side `md_dt.params = dt.params = []`.
      -- (b) Each dtStep on `dt' ∈ newDataTypes` either preserves the prior
      --     value at g (no inner-ctor collision) or overwrites with
      --     `.constructor { dt' with constructors := rwCtors_of_dt' } c''`.
      --     Drain invariant `NewDtFullShape` forces `dt'.params = []`, so
      --     the override has `params = []` too.
      -- (c) Each fnStep on `f ∈ newFunctions` writes `.function _` at f.name.
      --     `hFnNotKey` rules out f.name = g, so g is preserved across fnStep.
      --
      -- Drain invariant: all `dt' ∈ drained.newDataTypes` have `dt'.params = []`
      -- (from `NewDtFullShape`'s canonical instantiation form).
      have hNewDtFull : drained.NewDtFullShape tds :=
        concretize_drain_preserves_NewDtFullShape _ _
          (DrainState.NewDtFullShape.init tds (concretizeSeed tds)) hdrain
      have hAllNewDtParamsEmpty : ∀ dt' ∈ drained.newDataTypes, dt'.params = [] := by
        intro dt' hmem
        obtain ⟨_, _, _, _, _, _, hshape⟩ := hNewDtFull dt' hmem
        rw [hshape]
      -- Predicate: a typed declaration at `g` is `.constructor X _` with `X.params = []`.
      let CtorParamsEmpty : Typed.Declaration → Prop :=
        fun d => ∃ X Y, d = .constructor X Y ∧ X.params = []
      -- Step (a): srcStep fold's explicit value at g has params = [].
      have hsrc_explicit := PhaseA2.fromSource_inserts_ctor_at_key_explicit
        tds drained.mono htd_c hparams_eq
      -- The above gives:
      -- `(tds.pairs.foldl srcStep default).getByKey g =
      --    some (.constructor { dt with constructors := rwCtors }
      --                       { c with argTypes := ... })`.
      simp only at hsrc_explicit
      let rwCtors_dt : List Constructor := dt.constructors.map fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
      let newDt_src : DataType := { dt with constructors := rwCtors_dt }
      let newCtor_src : Constructor :=
        { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
      have hsrc_get : ∃ X Y,
          (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default).getByKey g =
            some (.constructor X Y) ∧ X.params = [] :=
        ⟨newDt_src, newCtor_src, hsrc_explicit, hparams_eq⟩
      -- Generic insert preservation of CtorParamsEmpty at g.
      have hinsert_pres_CPE : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
          (k = g → CtorParamsEmpty v) →
          (∃ d, acc.getByKey g = some d ∧ CtorParamsEmpty d) →
          (∃ d, (acc.insert k v).getByKey g = some d ∧ CtorParamsEmpty d) := by
        intro acc k v hkv ⟨d, hget_d, hCPE⟩
        by_cases hbeq : (k == g) = true
        · have hkeq : k = g := LawfulBEq.eq_of_beq hbeq
          refine ⟨v, ?_, hkv hkeq⟩
          rw [hkeq]; exact IndexMap.getByKey_insert_self _ _ _
        · have hne : (k == g) = false := Bool.not_eq_true _ |>.mp hbeq
          exact ⟨d, by
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget_d, hCPE⟩
      -- Per-step preservation across dtStep on `dt' ∈ newDataTypes`.
      -- The dtStep writes `.dataType { dt' with ...}` at dt'.name (params=[])
      -- and `.constructor { dt' with ...} c''` at dt'.name.pushNs (params=[]).
      have hdtStep_pres_CPE : ∀ (acc : Typed.Decls) (dt' : DataType),
          dt' ∈ drained.newDataTypes →
          (∃ d, acc.getByKey g = some d ∧ CtorParamsEmpty d) →
          (∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey g = some d ∧
            CtorParamsEmpty d) := by
        intro acc dt' hdt'_mem hacc
        unfold PhaseA2.dtStep
        let emptySubst : Global → Option Typ := fun _ => none
        let rwCtors_dt' : List Constructor := dt'.constructors.map fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst drained.mono) }
        let newDt' : DataType := { dt' with constructors := rwCtors_dt' }
        have hdt'_params : dt'.params = [] := hAllNewDtParamsEmpty dt' hdt'_mem
        -- First insert: at dt'.name with `.dataType newDt'`.
        have hafter_dt_name : ∃ d,
            (acc.insert dt'.name (.dataType newDt')).getByKey g = some d ∧
              CtorParamsEmpty d := by
          apply hinsert_pres_CPE acc dt'.name (.dataType newDt')
          · -- If dt'.name = g, the value is `.dataType _` which doesn't satisfy
          --   `CtorParamsEmpty` (it's not `.constructor`). But `hDtNotKey`
          --   rules out dt'.name = g.
            intro hkey_eq_g
            exfalso; exact hDtNotKey dt' hdt'_mem hkey_eq_g
          · exact hacc
        -- Inner ctor fold: each insert is at `dt'.name.pushNs c''.nameHead`
        -- with `.constructor newDt' c''`.
        suffices h : ∀ (cs : List Constructor) (acc' : Typed.Decls),
            (∃ d, acc'.getByKey g = some d ∧ CtorParamsEmpty d) →
            (∃ d, (cs.foldl
              (fun acc'' c'' =>
                acc''.insert (dt'.name.pushNamespace c''.nameHead)
                  (.constructor newDt' c'')) acc').getByKey g = some d ∧
              CtorParamsEmpty d) by
          exact h rwCtors_dt' _ hafter_dt_name
        intro cs
        induction cs with
        | nil => intro _ h; exact h
        | cons c'' rest ih =>
          intro acc' hacc'
          simp only [List.foldl_cons]
          apply ih
          apply hinsert_pres_CPE acc' (dt'.name.pushNamespace c''.nameHead)
            (.constructor newDt' c'')
          · -- The inserted value is .constructor newDt' c'' with newDt'.params = []
            intro _
            refine ⟨newDt', c'', rfl, ?_⟩
            show ({ dt' with constructors := rwCtors_dt' } : DataType).params = []
            exact hdt'_params
          · exact hacc'
      -- dtStep fold preservation.
      have hdtFold_pres_CPE : ∀ (xs : List DataType),
          (∀ dt' ∈ xs, dt' ∈ drained.newDataTypes) →
          ∀ (init : Typed.Decls),
            (∃ d, init.getByKey g = some d ∧ CtorParamsEmpty d) →
            (∃ d, (xs.foldl (PhaseA2.dtStep drained.mono) init).getByKey g = some d ∧
              CtorParamsEmpty d) := by
        intro xs
        induction xs with
        | nil => intro _ init h; exact h
        | cons hd tl ih =>
          intro hMem init h
          simp only [List.foldl_cons]
          apply ih (fun dt' hdt' => hMem dt' (List.mem_cons_of_mem _ hdt'))
          exact hdtStep_pres_CPE init hd (hMem hd List.mem_cons_self) h
      -- fnStep on `f ∈ newFunctions`: writes `.function _` at f.name.
      -- `hFnNotKey` ⇒ f.name ≠ g, so g is preserved.
      have hfnStep_pres_CPE : ∀ (acc : Typed.Decls) (f : Typed.Function),
          f ∈ drained.newFunctions →
          (∃ d, acc.getByKey g = some d ∧ CtorParamsEmpty d) →
          (∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey g = some d ∧
            CtorParamsEmpty d) := by
        intro acc f hf_mem hacc
        unfold PhaseA2.fnStep
        apply hinsert_pres_CPE acc f.name
        · intro hkey_eq_g
          exfalso; exact hFnNotKey f hf_mem hkey_eq_g
        · exact hacc
      -- fnStep fold preservation.
      have hfnFold_pres_CPE : ∀ (xs : List Typed.Function),
          (∀ f ∈ xs, f ∈ drained.newFunctions) →
          ∀ (init : Typed.Decls),
            (∃ d, init.getByKey g = some d ∧ CtorParamsEmpty d) →
            (∃ d, (xs.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey g = some d ∧
              CtorParamsEmpty d) := by
        intro xs
        induction xs with
        | nil => intro _ init h; exact h
        | cons hd tl ih =>
          intro hMem init h
          simp only [List.foldl_cons]
          apply ih (fun f hf => hMem f (List.mem_cons_of_mem _ hf))
          exact hfnStep_pres_CPE init hd (hMem hd List.mem_cons_self) h
      -- Compose: srcStep fold → dtStep fold → fnStep fold yields CtorParamsEmpty at g.
      have hsrc_init : ∃ d,
          (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default).getByKey g =
            some d ∧ CtorParamsEmpty d := by
        obtain ⟨X, Y, hget_X, hX_params⟩ := hsrc_get
        exact ⟨_, hget_X, X, Y, rfl, hX_params⟩
      have hcb_CPE : ∃ d,
          (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).getByKey g = some d ∧ CtorParamsEmpty d := by
        rw [PhaseA2.concretizeBuild_eq]
        rw [show drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
              (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default)
            = drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default)
          from by rw [← Array.foldl_toList]]
        rw [show drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono)
              (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
            = drained.newFunctions.toList.foldl (PhaseA2.fnStep tds drained.mono)
                (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                  (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
          from by rw [← Array.foldl_toList]]
        apply hfnFold_pres_CPE
        · intro f hf; exact Array.mem_toList_iff.mp hf
        apply hdtFold_pres_CPE
        · intro dt' hdt'; exact Array.mem_toList_iff.mp hdt'
        exact hsrc_init
      -- Combine with hget_md: the value at g is `.constructor md_dt md_c`,
      -- but also `.constructor X Y` with `X.params = []`. By IndexMap value
      -- uniqueness (same key, same value), `md_dt = X`.
      obtain ⟨d, hget_d, X, Y, hd_eq, hX_params⟩ := hcb_CPE
      rw [hget_md] at hget_d
      subst hd_eq
      simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget_d
      obtain ⟨hX_md, _⟩ := hget_d
      -- `X = md_dt`, hence `md_dt.params = X.params = []`.
      exact Or.inl (List.isEmpty_iff.mpr (hX_md ▸ hX_params))
    · -- Arms B/C/D: tArgs.nonempty. Output disjunct trivially via `Or.inr`
      -- since `tArgs.map`-rewriting preserves `.size` (and hence `.isEmpty`).
      simp only [Bool.not_eq_true] at htArgs
      have htArgs' : ¬ (tArgs.map (rewriteTyp (fun _ => none) drained.mono)).isEmpty := by
        rw [htArgs_isEmpty_iff]; intro h; exact absurd h (by simp [htArgs])
      cases hpop : g.popNamespace with
      | none =>
        -- Arm B: popNamespace = none. UNREACHABLE per mkDecls_source_ctor_is_key.
        exfalso
        rw [hkey_eq] at hpop
        unfold Global.pushNamespace Global.popNamespace at hpop
        simp at hpop
      | some sndPair =>
        obtain ⟨ctorName, parent⟩ := sndPair
        cases hmono : drained.mono[(dt.name, tArgs)]? with
        | none =>
          -- Arm C: mono-miss. rewriteGlobal returns `g`.
          have hrwg_eq : rewriteGlobal tds drained.mono g tArgs = g := by
            unfold rewriteGlobal; rw [if_neg (by simp [htArgs]), htd_c]
            simp [hpop, hmono]
          rw [hrwg_eq]
          -- Sub-case split on `dt.params.isEmpty`:
          --
          --  • Arm C.mono (`dt.params = []`): `tArgs.nonempty` admitted by the
          --    bridge premise's universal quantifier, but `dt.params = []`
          --    means `srcStep` DOES insert at `g` (per
          --    `fromSource_inserts_ctor_at_key`). Disjointness via the
          --    Arm A pattern (`hSNN` + `hUnique` +
          --    `concretizeName_singleton_ref_simple`). CLOSED below by reusing
          --    Arm A's machinery.
          --  • Arm C.poly (`¬ dt.params.isEmpty`): `srcStep` SKIPS the poly
          --    ctor key, and dtStep can only insert at
          --    `dt'.name.pushNamespace c'.nameHead` for `dt' ∈
          --    drained.newDataTypes`. Combined with `hSNN.2`, `dt'.name =
          --    concretizeName g_d args_d` with `args_d.size = dt_orig.params.length`.
          --    For `dt'.name.pushNs c'.nameHead = g = dt.name.pushNs c.nameHead`
          --    to hold via the single-limb append (with `hUnique`), we'd need
          --    `g_d = dt.name ∧ args_d.push (.ref ⟨.mkSimple c'.nameHead⟩) =
          --    #[.ref ⟨.mkSimple c.nameHead⟩]`, which forces `args_d.size = 0`
          --    hence `dt_orig.params = []`. Then `dt = dt_orig` (key uniqueness)
          --    contradicts `¬ dt.params.isEmpty`. Discharged below as Arm C.poly.
          by_cases hparams_empty : dt.params.isEmpty
          · -- Arm C.mono: `dt.params = []`. Mirror Arm A's machinery.
            have hparams_eq : dt.params = [] := List.isEmpty_iff.mp hparams_empty
            -- Single-limb collision-arg shape, same as Arm A.
            let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
            have hg_concName_eq : g = concretizeName dt.name #[collisionArg] := by
              rw [RefClosedBody.concretizeName_singleton_ref_simple, hkey_eq]
            -- `g` is a key in concretizeBuild output: srcStep inserts at `g`,
            -- subsequent folds preserve `containsKey g`.
            obtain ⟨_, _, hsrc_get_g⟩ :=
              PhaseA2.fromSource_inserts_ctor_at_key tds drained.mono htd_c hparams_eq
            have hsrc_contains_g : (tds.pairs.foldl
                (PhaseA2.srcStep tds drained.mono) default).containsKey g :=
              (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hsrc_get_g]; rfl)
            have hmono_contains_g : (concretizeBuild tds drained.mono drained.newFunctions
                drained.newDataTypes).containsKey g := by
              rw [PhaseA2.concretizeBuild_eq]
              apply PhaseA2.fnStep_foldl_preserves_containsKey
              apply PhaseA2.dtStep_foldl_preserves_containsKey
              exact hsrc_contains_g
            have hcd_contains_g : cd.containsKey g := (hkeys g).mp hmono_contains_g
            have hg_in_cd : ∃ d, cd.getByKey g = some d := by
              rcases h : cd.getByKey g with _ | d
              · exact absurd ((IndexMap.getByKey_isSome_iff_containsKey _ _).mpr
                  hcd_contains_g) (by rw [h]; intro h'; cases h')
              · exact ⟨d, rfl⟩
            -- `hDtNotKey`: same machinery as Arm A.
            have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
              intro dt' hdt'_mem heq
              obtain ⟨g_d, args_d, dt_orig, hd_name, hd_get, hd_sz, _⟩ := hSNN.2 dt' hdt'_mem
              have heq_concName :
                  concretizeName g_d args_d = concretizeName dt.name #[collisionArg] := by
                rw [← hd_name, heq, hg_concName_eq]
              have hCdKey : ∃ d, cd.getByKey (concretizeName g_d args_d) = some d := by
                rw [heq_concName, ← hg_concName_eq]; exact hg_in_cd
              obtain ⟨hg_eq, hargs_eq⟩ :=
                hUnique hconc_orig g_d dt.name args_d #[collisionArg] heq_concName hCdKey
              obtain ⟨_hsrc_dt, _⟩ := mkDecls_ctor_companion hdecls g dt c hsrc_ctor
              have hd_get_decls : decls.getByKey g_d = some (.dataType dt_orig) :=
                hTdDt g_d dt_orig hd_get
              rw [hg_eq] at hd_get_decls
              rw [_hsrc_dt] at hd_get_decls
              simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hd_get_decls
              have hd_orig_params : dt_orig.params = [] := by
                rw [← hd_get_decls]; exact hparams_eq
              have hsz_zero : args_d.size = 0 := by
                rw [hd_sz, hd_orig_params]; rfl
              have hsz_one : args_d.size = 1 := by
                rw [hargs_eq]; rfl
              omega
            -- `hFnNotKey`: same pattern as Arm A.
            have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
              intro f hf heq
              obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
              have heq_concName :
                  concretizeName g_f args_f = concretizeName dt.name #[collisionArg] := by
                rw [← hf_name, heq, hg_concName_eq]
              have hCdKey : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
                rw [heq_concName, ← hg_concName_eq]; exact hg_in_cd
              obtain ⟨hg_eq, _hargs_eq⟩ :=
                hUnique hconc_orig g_f dt.name args_f #[collisionArg] heq_concName hCdKey
              obtain ⟨_hsrc_dt, _⟩ := mkDecls_ctor_companion hdecls g dt c hsrc_ctor
              obtain ⟨td_dt', htd_dt'⟩ := checkAndSimplify_src_dt_to_td hdecls hts _hsrc_dt
              rw [hg_eq] at hf_get
              rw [hf_get] at htd_dt'
              cases htd_dt'
            -- Apply kind-fwd with `dt.params = []`.
            obtain ⟨md_dt, md_c, hget_md⟩ :=
              PhaseA2.concretizeBuild_preserves_ctor_kind_fwd tds drained.mono
                drained.newFunctions drained.newDataTypes htd_c hparams_eq
                hDtNotKey hFnNotKey
            -- Output disjunct: `tArgs.nonempty` ⇒ `Or.inr` discharges.
            exact ⟨md_dt, md_c, hget_md, Or.inr htArgs'⟩
          · -- Arm C.poly: `¬ dt.params.isEmpty`. Closed via the
            -- body-witness threaded through the bridge premise.
            --
            -- With `tArgs.nonempty` and `dt.params != []` (polymorphic source
            -- ctor), `rewriteGlobal` returns the source ctor key `g` itself.
            -- The bridge's body-witness premise tells us `(g, tArgs)` appears
            -- as a `.ref` site of either a monomorphic source-function body
            -- (with `f_src.params = []`) or a `drained.newFunctions` body.
            -- Either way, `drain_populates_mono_for_body_ref_polymorphic`
            -- gives us `(dt.name, tArgs) ∈ drained.mono.contains`, which
            -- contradicts `hmono : drained.mono[(dt.name, tArgs)]? = none`.
            exfalso
            have hpoly_ne : ¬ dt.params.isEmpty := hparams_empty
            have htArgs_ne : ¬ tArgs.isEmpty := by simp [htArgs]
            have hContains : drained.mono.contains (dt.name, tArgs) :=
              drain_populates_mono_for_body_ref_polymorphic hdrain g tArgs dt c
                htd_c htArgs_ne hpoly_ne hBodyWitness
            -- `mono.contains` ⇒ `mono[..]?.isSome`. But `hmono` says it's `none`.
            rw [Std.HashMap.contains_eq_isSome_getElem?] at hContains
            rw [hmono] at hContains
            cases hContains
        | some concDTName =>
          -- Arm D: mono-hit. rewriteGlobal returns `concDTName.pushNamespace ctorName`.
          have hrwg_eq : rewriteGlobal tds drained.mono g tArgs =
              concDTName.pushNamespace ctorName := by
            unfold rewriteGlobal; rw [if_neg (by simp [htArgs]), htd_c]
            simp [hpop, hmono]
          rw [hrwg_eq]
          -- Derive ctorName = c.nameHead, parent = dt.name from hpop + hkey_eq.
          have hpop_eq : (g.popNamespace, g) = (some (c.nameHead, dt.name),
              dt.name.pushNamespace c.nameHead) := by
            rw [hkey_eq]
            constructor
          obtain ⟨hpop_decompose, _⟩ := Prod.mk.inj hpop_eq
          rw [hpop] at hpop_decompose
          simp only [Option.some.injEq, Prod.mk.injEq] at hpop_decompose
          obtain ⟨hctorName_eq, _hparent_eq⟩ := hpop_decompose
          -- Lift dt-companion to typed.
          obtain ⟨_hsrc_dt, hcmem⟩ :=
            mkDecls_ctor_companion hdecls g dt c hsrc_ctor
          obtain ⟨td_dt', htd_dt'⟩ :=
            checkAndSimplify_src_dt_to_td hdecls hts _hsrc_dt
          have hsrc_dt_again : decls.getByKey dt.name = some (.dataType td_dt') :=
            (hFnMatchP dt.name).2.1 td_dt' htd_dt'
          rw [_hsrc_dt] at hsrc_dt_again
          simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hsrc_dt_again
          subst hsrc_dt_again
          -- MonoShapeOk gives newDt ∈ drained.newDataTypes.
          obtain ⟨newDt, hnewDt_mem, hnewDt_name, hnewDt_ctors⟩ :=
            hMSO dt.name tArgs concDTName hmono htd_dt'
          -- Identify newC ∈ newDt.constructors with newC.nameHead = c.nameHead.
          have hnewC_exists : ∃ newC ∈ newDt.constructors, newC.nameHead = c.nameHead := by
            rw [hnewDt_ctors]
            refine ⟨_, List.mem_map.mpr ⟨c, hcmem, rfl⟩, rfl⟩
          obtain ⟨newC, hnewC_mem, hnewC_nh⟩ := hnewC_exists
          -- Target key equality.
          have hkey_target : concDTName.pushNamespace ctorName =
              newDt.name.pushNamespace newC.nameHead := by
            rw [hnewDt_name, hnewC_nh, hctorName_eq]
          rw [hkey_target]
          -- Closure pattern from `SizeBound.lean:1715-1820`. The target key
          -- `K = newDt.name.pushNamespace newC.nameHead` is expressed as
          -- `concretizeName g_outer (args_outer.push collisionArg)` via the
          -- single-limb identity. Combined with `hSNN` on a candidate `dt'`
          -- (or `f`), `hUnique` forces argument-size mismatch (or kind clash).
          -- First, express `K = newDt.name.pushNamespace newC.nameHead` as a
          -- concretizeName-append of `newDt`'s push origin (g_outer, args_outer).
          obtain ⟨g_outer, args_outer, dt_orig_outer, hd_name_o, hd_get_o, hd_sz_o,
                  _hctors_o⟩ := hSNN.2 newDt hnewDt_mem
          let collisionArg_D : Typ := .ref ⟨.mkSimple newC.nameHead⟩
          have hK_eq : newDt.name.pushNamespace newC.nameHead =
              concretizeName g_outer (args_outer.push collisionArg_D) := by
            rw [← RefClosedBody.concretizeName_singleton_ref_simple
              newDt.name newC.nameHead, hd_name_o]
            show concretizeName (concretizeName g_outer args_outer) #[collisionArg_D]
              = (args_outer.push collisionArg_D).foldl Typ.appendNameLimbs g_outer
            unfold concretizeName
            show #[collisionArg_D].foldl Typ.appendNameLimbs
              (args_outer.foldl Typ.appendNameLimbs g_outer) =
              (args_outer.push collisionArg_D).foldl Typ.appendNameLimbs g_outer
            rw [Array.foldl_push]
            rfl
          -- Prove the target key is in `cd`. Trace: `dtStep` on `newDt`
          -- inserts at the key; subsequent dt/fn folds preserve; step4Lower
          -- preserves kind (and existence).
          have hK_in_mono : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
              drained.newDataTypes).getByKey
                (newDt.name.pushNamespace newC.nameHead) = some d := by
            rw [PhaseA2.concretizeBuild_eq]
            -- Key persistence after dtStep on `newDt`.
            have hmem' : newDt ∈ drained.newDataTypes.toList :=
              Array.mem_toList_iff.mpr hnewDt_mem
            obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
            -- Generic preservation across insert.
            have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
                (∃ d, acc.getByKey (newDt.name.pushNamespace newC.nameHead) = some d) →
                ∃ d, (acc.insert k v).getByKey
                  (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro acc k v ⟨d, hget_d⟩
              by_cases hbeq : (k == newDt.name.pushNamespace newC.nameHead) = true
              · have hkeq : k = newDt.name.pushNamespace newC.nameHead :=
                  LawfulBEq.eq_of_beq hbeq
                rw [hkeq]; exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
              · have hne : (k == newDt.name.pushNamespace newC.nameHead) = false :=
                  Bool.not_eq_true _ |>.mp hbeq
                exact ⟨d, by
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget_d⟩
            have hinner_pres : ∀ (acc : Typed.Decls) (innerDt : DataType)
                (dt_outer : DataType) (cs : List Constructor),
                (∃ d, acc.getByKey (newDt.name.pushNamespace newC.nameHead) = some d) →
                ∃ d, (cs.foldl
                  (fun acc'' c =>
                    acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                      (.constructor innerDt c)) acc).getByKey
                    (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro acc innerDt dt_outer cs hacc
              induction cs generalizing acc with
              | nil => exact hacc
              | cons c rest ih =>
                simp only [List.foldl_cons]
                apply ih
                exact hinsert_pres acc _ _ hacc
            have hdt_pres : ∀ (acc : Typed.Decls) (dt_x : DataType),
                (∃ d, acc.getByKey (newDt.name.pushNamespace newC.nameHead) = some d) →
                ∃ d, (PhaseA2.dtStep drained.mono acc dt_x).getByKey
                  (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro acc dt_x hacc
              simp only [PhaseA2.dtStep]
              apply hinner_pres
              exact hinsert_pres acc _ _ hacc
            have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
                (∃ d, acc.getByKey (newDt.name.pushNamespace newC.nameHead) = some d) →
                ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey
                  (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro acc f ⟨d, hget_d⟩
              unfold PhaseA2.fnStep
              by_cases hbeq : (f.name == newDt.name.pushNamespace newC.nameHead) = true
              · have hkeq : f.name = newDt.name.pushNamespace newC.nameHead :=
                  LawfulBEq.eq_of_beq hbeq
                rw [hkeq]; exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
              · have hne : (f.name == newDt.name.pushNamespace newC.nameHead) = false :=
                  Bool.not_eq_true _ |>.mp hbeq
                exact ⟨d, by
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget_d⟩
            have hat_newDt_step : ∀ (init : Typed.Decls),
                ∃ d, (PhaseA2.dtStep drained.mono init newDt).getByKey
                  (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro init
              obtain ⟨_, _, hget_at⟩ :=
                PhaseA2.dtStep_inserts_ctor_at_self_ctor drained.mono init newDt hnewC_mem
              exact ⟨_, hget_at⟩
            have hdt_fold_pres : ∀ (xs : List DataType) (init : Typed.Decls),
                (∃ d, init.getByKey (newDt.name.pushNamespace newC.nameHead) = some d) →
                ∃ d, (xs.foldl (PhaseA2.dtStep drained.mono) init).getByKey
                  (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro xs
              induction xs with
              | nil => intro init h; exact h
              | cons hd tl ih =>
                intro init h
                simp only [List.foldl_cons]
                exact ih _ (hdt_pres _ _ h)
            have hfn_fold_pres : ∀ (xs : List Typed.Function) (init : Typed.Decls),
                (∃ d, init.getByKey (newDt.name.pushNamespace newC.nameHead) = some d) →
                ∃ d, (xs.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey
                  (newDt.name.pushNamespace newC.nameHead) = some d := by
              intro xs
              induction xs with
              | nil => intro init h; exact h
              | cons hd tl ih =>
                intro init h
                simp only [List.foldl_cons]
                exact ih _ (hfn_pres _ _ h)
            -- Compose: pre fold → newDt step → post fold → fn fold.
            repeat rw [← Array.foldl_toList]
            rw [hsplit, List.foldl_append, List.foldl_cons]
            apply hfn_fold_pres
            apply hdt_fold_pres
            exact hat_newDt_step _
          have hK_in_cd : ∃ d, cd.getByKey
              (newDt.name.pushNamespace newC.nameHead) = some d := by
            obtain ⟨d_mono, hmono_get⟩ := hK_in_mono
            have h_kind := step4Lower_fold_kind_at_key hmono_get hconc
            cases d_mono with
            | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
            | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
            | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
          -- `hDtNotKey` (Arm D): if `dt'.name = K`, hSNN.2 gives
          -- `dt'.name = concretizeName g_d args_d`. Then concretizeName equality
          -- rewrites to `concretizeName g_d args_d = concretizeName g_outer
          -- (args_outer.push collisionArg)`. hUnique forces `g_d = g_outer`,
          -- collapsing `dt_orig = dt_orig_outer` (key uniqueness in tds), and
          -- forcing `args_d.size = args_outer.size + 1`. But also
          -- `args_d.size = dt_orig.params.length = dt_orig_outer.params.length =
          -- args_outer.size`, contradiction.
          have hDtNotKey : ∀ dt' ∈ drained.newDataTypes,
              dt'.name ≠ newDt.name.pushNamespace newC.nameHead := by
            intro dt' hdt'_mem heq
            obtain ⟨g_d, args_d, dt_orig, hd_name, hd_get, hd_sz, _⟩ :=
              hSNN.2 dt' hdt'_mem
            have heq_concName :
                concretizeName g_d args_d =
                  concretizeName g_outer (args_outer.push collisionArg_D) := by
              rw [← hd_name, heq, hK_eq]
            have hCdKey :
                ∃ d, cd.getByKey (concretizeName g_d args_d) = some d := by
              rw [heq_concName, ← hK_eq]; exact hK_in_cd
            obtain ⟨hg_eq, hargs_eq⟩ :=
              hUnique hconc_orig g_d g_outer args_d (args_outer.push collisionArg_D)
                heq_concName hCdKey
            -- Key uniqueness in tds: `g_d = g_outer` ⇒ `dt_orig = dt_orig_outer`.
            rw [hg_eq] at hd_get
            rw [hd_get] at hd_get_o
            simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hd_get_o
            have h_sz_lhs : args_d.size = dt_orig.params.length := hd_sz
            have h_sz_rhs : args_d.size = args_outer.size + 1 := by
              rw [hargs_eq, Array.size_push]
            have h_sz_outer : args_outer.size = dt_orig_outer.params.length := hd_sz_o
            rw [hd_get_o] at h_sz_lhs
            omega
          -- `hFnNotKey` (Arm D): same equation reasoning forces `g_f = g_outer`,
          -- but `tds[g_f] = .function f_orig` while `tds[g_outer] = .dataType _`,
          -- giving an immediate kind clash.
          have hFnNotKey : ∀ f ∈ drained.newFunctions,
              f.name ≠ newDt.name.pushNamespace newC.nameHead := by
            intro f hf heq
            obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
            have heq_concName :
                concretizeName g_f args_f =
                  concretizeName g_outer (args_outer.push collisionArg_D) := by
              rw [← hf_name, heq, hK_eq]
            have hCdKey :
                ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
              rw [heq_concName, ← hK_eq]; exact hK_in_cd
            obtain ⟨hg_eq, _hargs_eq⟩ :=
              hUnique hconc_orig g_f g_outer args_f (args_outer.push collisionArg_D)
                heq_concName hCdKey
            rw [hg_eq] at hf_get
            rw [hf_get] at hd_get_o
            cases hd_get_o
          have hget := PhaseA2.concretizeBuild_at_newDt_ctor_name tds drained.mono
            drained.newFunctions drained.newDataTypes
            hnewDt_mem hnewC_mem hDtNotKey hFnNotKey
          -- Output disjunct: `tArgs.nonempty` ⇒ `Or.inr` discharges.
          obtain ⟨md_dt, md_c, hget_md⟩ := hget
          exact ⟨md_dt, md_c, hget_md, Or.inr htArgs'⟩
  have hmdRef : Typed.Decls.TermRefsDt
      (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes) :=
    concretizeBuild_preserves_TermRefsDt htdsRef hnfRef hRefsBridge
  -- Stage 4 (step4Lower fold): concrete-side TermRefsDt.
  exact step4Lower_fold_preserves_TermRefsDt hmdRef hconc

end Aiur

end -- public section
