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

Sig amendment 2026-05-04: `concretizeBuild_preserves_TermRefsDt` takes
the bridge predicate as an explicit hypothesis, keeping its body trivial
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

Sig amendment 2026-05-04: bridge promoted from internal sub-claim (sorried
in the upstream `RefsDt.lean` due to import-order constraints) to explicit
caller-supplied hypothesis. The relocated theorem is sorry-free; the
discharge of `_hRefsBridge` at `concretize_preserves_TermRefsDt` is the
remaining structural work, owned by that consumer. -/
theorem concretizeBuild_preserves_TermRefsDt
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (htdsRef : Typed.Decls.TermRefsDt typedDecls)
    (hnfRef : ∀ f ∈ newFunctions, Typed.Term.RefsDt typedDecls f.body)
    -- Sig amendment 2026-05-04 (RefsDt-defect): bridge premise now threads
    -- the structural disjunct `dt.params.isEmpty ∨ ¬ tArgs.isEmpty` in both
    -- input and output, paralleling the `Typed.Term.RefsDt.ref` field. The
    -- output's `tArgs` is `tArgs.map (rewriteTyp ...)`, which preserves
    -- `.size` (and hence `.isEmpty`); we use `Typ.instantiate (fun _ => none)`
    -- as the substitution to match `rewriteTypedTerm`'s `emptySubst` call
    -- pattern at the consumer site (`concretizeBuild_function_origin_with_body`
    -- uses `emptySubst : fun _ => none`).
    (_hRefsBridge : ∀ g tArgs,
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
    obtain ⟨f_src, hsrc_get, _hparams, hbody_eq⟩ := h_src
    rw [hbody_eq]
    have hf_src_RefsDt : Typed.Term.RefsDt typedDecls f_src.body :=
      htdsRef g f_src hsrc_get
    exact rewriteTypedTerm_preserves_RefsDt (mono := mono)
      (decls := typedDecls) hf_src_RefsDt _hRefsBridge
  · -- newFunctions origin.
    obtain ⟨f_nf, hf_mem, _hname, hbody_eq⟩ := h_nf
    rw [hbody_eq]
    exact rewriteTypedTerm_preserves_RefsDt (mono := mono)
      (decls := typedDecls) (hnfRef f_nf hf_mem) _hRefsBridge

/-! ### `step4Lower` fold: typed-side → concrete-side `TermRefsDt`. -/

/-- `step4Lower` fold lifts `Typed.Decls.TermRefsDt monoDecls` to
`Concrete.Decls.TermRefsDt cd` — assembled via `step4Lower_fold_function_origin`
(F=0 in `RefsDt.lean`), `step4Lower_fold_dataType_bridge_inline` /
`step4Lower_fold_ctor_bridge_inline` (F=0 in `Shapes.lean`) for the dt/ctor
bridge, and `termToConcrete_preserves_RefsDt`. Relocated 2026-05-04 to
co-locate with `concretizeBuild_preserves_TermRefsDt`. -/
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
impossible under well-formed Aiur — `refLookup` (`Check.lean:421`) only
produces `.ref` for nullary ctors, and `tArgs` is always pinned to
`dt.params.length` at the type-checker. The corresponding mono lookup is
populated by the drain process whenever the ctor reaches a body
(BodyAppRefToDt + drain reachability). The bridge's full discharge at
this site under the existing reachability infrastructure is currently
planted as a single granular sub-sorry (`BLOCKED-RefsDt-Bridge`) pending
the drain-completeness chain.

Relocated 2026-05-04 from `Shapes.lean` to co-locate with
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
  -- Stage 3 (concretizeBuild): typed-side TermRefsDt on the resulting monoDecls.
  -- Sig amendment 2026-05-04 (RefsDt-defect): `Typed.Term.RefsDt`'s `.ref` arm
  -- now carries the structural disjunct `dt.params.isEmpty ∨ ¬ tArgs.isEmpty`
  -- (refLookup at Check.lean:421 emits `.ref g #[]` only for mono ctors and
  -- `.ref g mvars` with `mvars.size = dt.params.length > 0` for poly ctors).
  -- The bridge premise here threads the disjunct through: input includes the
  -- disjunct, output produces it post-rewrite. With this amendment, Arm A.ctor
  -- can extract `dt.params = []` from the input and apply
  -- `concretizeBuild_preserves_ctor_kind_fwd` directly — no more structural
  -- incompatibility blocker for that arm.
  have hRefsBridge : ∀ g tArgs,
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
    intro g tArgs ⟨dt, c, htd_c, hdisj⟩
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
      -- Sig amendment 2026-05-04 (RefsDt-defect): from `tArgs.isEmpty` and
      -- the new disjunct `dt.params.isEmpty ∨ ¬ tArgs.isEmpty`, extract
      -- `dt.params.isEmpty`. This is the analytical content of the
      -- `Typed.Term.RefsDt`-defect amendment: `refLookup` (Check.lean:421-441)
      -- emits `.ref g #[]` only when `dt.params.isEmpty`.
      have hparams_empty : dt.params.isEmpty := by
        rcases hdisj with h | h
        · exact h
        · exfalso; exact h htArgs
      have hparams_eq : dt.params = [] := List.isEmpty_iff.mp hparams_empty
      -- BLOCKED-RefsDt-Bridge-A-disjoint: still need StrongNewNameShape
      -- disjointness (no `dt' ∈ drained.newDataTypes` or `f ∈ drained.newFunctions`
      -- has `name = g`). Closure pattern parallels Arm D's disjointness, see
      -- `SizeBound.lean:1715-1820`: express `g = dt.name.pushNamespace c.nameHead`
      -- as `concretizeName _ #[collisionArg]` (single-limb), then apply
      -- `ConcretizeUniqueNames` (drain invariant via `hUnique`) to force
      -- argument-size mismatch. Sig amendment to take `WellFormed t` would
      -- expose `ConcretizeUniqueNames` directly.
      have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
        sorry
      have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
        sorry
      -- Apply kind-fwd with the extracted `dt.params = []`.
      obtain ⟨md_dt, md_c, hget_md⟩ :=
        PhaseA2.concretizeBuild_preserves_ctor_kind_fwd tds drained.mono
          drained.newFunctions drained.newDataTypes htd_c hparams_eq
          hDtNotKey hFnNotKey
      refine ⟨md_dt, md_c, hget_md, ?_⟩
      -- Output disjunct: discharge via `Or.inr`-impossibility from `tArgs.isEmpty`,
      -- so we need `Or.inl md_dt.params.isEmpty`. The current kind-fwd doesn't
      -- promise param preservation; plant as a granular sub-sorry.
      -- BLOCKED-RefsDt-Bridge-A-md-params: `md_dt.params = []` from
      -- `concretizeBuild_preserves_ctor_kind_fwd`'s extension via
      -- `fromSource_inserts_ctor_at_key_explicit` (CtorKind.lean:813), which
      -- shows the post-fold `md_dt = { td_dt with constructors := rewrittenCtors }`,
      -- preserving `params`. The `_explicit` lemma exists; threading its result
      -- through to the existential here requires using it instead of the
      -- pure-existential `_fwd` variant. ~30 LoC adjustment.
      sorry
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
          -- BLOCKED-RefsDt-Bridge-C-mono-miss: rewriteGlobal returns `g` (poly
          -- ctor name) NOT in monoDecls. Discharge requires drain-reachability:
          -- every body-ref `.ref g tArgs` site has `(dt.name, tArgs) ∈ mono`.
          sorry
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
          -- BLOCKED-RefsDt-Bridge-D-disjoint: discharge disjointness premises
          -- (no newDt' / newFn collides with the target inner-ctor key).
          -- Closure requires StrongNewNameShape uniqueness without FullyMono;
          -- pattern in `SizeBound.lean:1715-1820` uses
          -- `RefClosedBody.concretizeName_singleton_ref_simple` to express the
          -- pushNamespace-key as a `concretizeName _ #[collisionArg]` then
          -- applies `ConcretizeUniqueNames` to force argument-size mismatch.
          -- Sig amendment to `WellFormed t` recommended.
          have hDtNotKey : ∀ dt' ∈ drained.newDataTypes,
              dt'.name ≠ newDt.name.pushNamespace newC.nameHead := by
            sorry
          have hFnNotKey : ∀ f ∈ drained.newFunctions,
              f.name ≠ newDt.name.pushNamespace newC.nameHead := by
            sorry
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
