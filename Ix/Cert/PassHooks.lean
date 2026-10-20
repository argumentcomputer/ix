import Ix.Cert.Statement
import Ix.CompileCert.RawRun

/-! # Pass 3's hooks on a block outside the changed set (Route A, B9b, piece 1)

`runBlockWithAux` runs Pass 3's hooks around a block's compile: hook 2
(`prepareBlock`) before it, which rewrites the members that reference an
image-kind head; hook 1 (`editBlock`) after the aux tail, inside
`compileBlockWithAux`; and `withMetaRefs`, which writes the decompile
records' extension references into the metadata. One lemma per hook, so a
later pass (batch 5) adds its own:

* `prepareBlock_unreferenced`: a block none of whose references (the
  condensation's, `CompileEnv.p3BlockRefs`) is a head is compiled from the
  compile environment as it is, and publishes nothing. (`prepareBlock`'s own
  walk over the terms, `headsIn`, is a `while` loop, which no proof unfolds;
  the condensation's references come first and decide it.)
* `withMetaRefs_records`: the metadata patch changes no record, byte or
  address.
* `runBlockWithAux_unreferenced`: so such a block's records are those of
  `compileBlockWithAux` run from the empty block state.

Hook 1 is not the identity on the block state: on a block that is not a plan
change it runs `editPermutedBelowFamily`, which moves a permuted
`IndPredBelow` family's auxiliaries to their display names. Those names are
in the changed set (the classifier counts the permuted family as a changed
component), and the hook runs after the block's `BlockResult` is computed, so
the block's own records are what `compileMutualBlock` returned. -/

namespace Ix.Cert.PassHooks

open Ix.CompileM

/-- A block's records: its block constant, bytes and address, and each
projection's name and constant (not their metadata). -/
def recordsOf (r : BlockResult) :
    Ixon.Constant × ByteArray × Address × Array (Ix.Name × Ixon.Constant) :=
  (r.block, r.blockBytes, r.blockAddr, r.projections.map fun p => (p.1, p.2.1))

/-- An `Id` search loop that finds nothing returns nothing. -/
theorem forIn_none_of {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false) →
      forIn (m := Id) l ((none : Option Bool), ()) (fun n _ =>
        if p n = true then pure (ForInStep.done (some true, ())) else pure (ForInStep.yield (none, ()))) =
        ((none : Option Bool), ())
  | [], _ => rfl
  | a :: l, h => by
    rw [List.forIn_cons]
    have ha := h a List.mem_cons_self
    simp only [ha, Bool.false_eq_true, ↓reduceIte, pure, bind]
    exact forIn_none_of p l fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- **Hook 2 on an unreferenced block is the identity**: when none of the
block's references (`p3BlockRefs`) is a head, `prepareBlock` returns the
compile environment as it is and publishes nothing. -/
theorem prepareBlock_unreferenced (cenv : CompileEnv) (all : Ix.Set Ix.Name) (lo : Ix.Name)
    (refs : Ix.Set Ix.Name) (hrefs : cenv.p3BlockRefs.get? lo = some refs)
    (hno : ∀ r ∈ refs.toList, cenv.p3Heads.contains r = false) :
    Ix.Compile.Pass.prepareBlock cenv all lo = .ok (cenv, {}) := by
  unfold Ix.Compile.Pass.prepareBlock
  split
  · rfl
  · dsimp only
    rw [hrefs]
    dsimp only
    rw [Std.HashSet.forIn_eq_forIn_toList, forIn_none_of _ _ hno]
    rfl

/-- **`withMetaRefs` changes no record**: only the metadata of the block or
its projections. -/
theorem withMetaRefs_records (refs : Std.HashMap Ix.Compile.ExactKey.ExactName MetaRefTable)
    (lo : Ix.Name) (r : BlockResult) :
    recordsOf (Ix.Compile.Pass.withMetaRefs refs lo r) = recordsOf r ∧
      (Ix.Compile.Pass.withMetaRefs refs lo r).classNames = r.classNames := by
  unfold Ix.Compile.Pass.withMetaRefs recordsOf
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · simp [Array.map_map, Function.comp_def]

/-- **A block hook 2 leaves alone compiles as `compileBlockWithAux`**, from
the empty block state, with the same records and class order (the metadata
aside). -/
theorem runBlockWithAux_unreferenced {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name}
    (prep : Ix.Compile.Pass.prepareBlock cenv all lo = .ok (cenv, {}))
    {r : BlockResult} {cache : BlockState} {layout? : Option Ixon.AuxLayout}
    {pub : Ix.Compile.Pass.Published}
    (h : runBlockWithAux cenv all lo = .ok (r, cache, layout?, pub)) :
    ∃ r' pub', CompileM.run cenv { all, current := lo, mutCtx := default, univCtx := [] } {}
        (compileBlockWithAux lo all) = .ok ((r', layout?, pub'), cache) ∧
      recordsOf r = recordsOf r' ∧ r.classNames = r'.classNames := by
  unfold runBlockWithAux at h
  rw [prep] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v hv
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨recs, cls⟩ := withMetaRefs_records v.2.p3MetaRefs lo v.1.1
    exact ⟨v.1.1, v.1.2.2, by rw [hv], recs, cls⟩

end Ix.Cert.PassHooks
