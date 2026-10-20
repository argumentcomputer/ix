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
  `compileBlockWithAux` run from the empty block state;
* `compileBlockWithAux_result`, `compileBlockWithAux_records`,
  `runBlockWithAux_records`: and those are the block compile's, a lone
  constant's `compileConstantInfo` or `sortConsts` then `compileMutualBlock`
  over the members, run from the empty block state (the member lookups and
  `MutConst.mkIndc` change no state, `mkIndc_preserves`): the form the reading
  theorems (N-READS) take. The aux tail and hook 1 run after the block's
  `BlockResult` is computed and return it as it is (`Returns`).

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


/-! ## What `compileBlockWithAux` returns -/

open Ix.CompileCert (rawRun rawRun_pure bind_ok)

/-- Every successful run of `m` returns a value with `P`. -/
def Returns {α : Type} (P : α → Prop) (m : CompileM α) : Prop :=
  ∀ ctx s x s', rawRun m ctx s = (.ok x, s') → P x

theorem Returns.pure {α : Type} {P : α → Prop} {x : α} (h : P x) : Returns P (pure x) := by
  intro ctx s y s' ran
  rw [rawRun_pure] at ran
  cases ran
  exact h

theorem Returns.bind {α β : Type} {P : α → Prop} {m : CompileM β} {k : β → CompileM α}
    (h : ∀ b, Returns P (k b)) : Returns P (m >>= k) := by
  intro ctx s x s' ran
  obtain ⟨b, mid, -, ran⟩ := bind_ok ran
  exact h b ctx mid x s' ran

theorem Returns.elim {α : Type} {P : α → Prop} {m : CompileM α} (hm : Returns P m)
    {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {x : α} : rawRun m ctx s = (.ok x, s') → P x :=
  hm ctx s x s'

theorem rawRun_ite {α : Type} {c : Prop} [Decidable c] {a b : CompileM α} {ctx : CompileEnv × BlockEnv}
    {s : BlockState} {r : Except CompileError α × BlockState}
    (h : rawRun (if c then a else b) ctx s = r) : rawRun a ctx s = r ∨ rawRun b ctx s = r := by
  by_cases hc : c
  · exact .inl (by simpa [hc] using h)
  · exact .inr (by simpa [hc] using h)


/-! ## The members' loop changes no state -/

open Ix.CompileCert (Preserves Preserves.bind Preserves.pure Preserves.throw Preserves.readCompile
  Preserves.forIn_list)

theorem findConst_preserves (n : Ix.Name) : Preserves id (findConst n) := by
  unfold findConst
  refine Preserves.bind (Preserves.readCompile id) fun env => ?_
  split
  · exact Preserves.pure id _
  · exact Preserves.throw id _

theorem collectMutConstConstructors_preserves :
    ∀ (names : List Ix.Name) (acc : Array ConstructorVal), Preserves id (collectMutConstConstructors names acc)
  | [], acc => Preserves.pure id acc
  | n :: rest, acc => by
    unfold collectMutConstConstructors
    refine Preserves.bind (findConst_preserves n) fun c => ?_
    split
    · exact collectMutConstConstructors_preserves rest _
    · exact Preserves.throw id _

theorem mkIndc_preserves (val : InductiveVal) : Preserves id (MutConst.mkIndc val) := by
  unfold MutConst.mkIndc
  exact Preserves.bind (collectMutConstConstructors_preserves _ _) fun _ => Preserves.pure id _

/-- **The block `compileBlockWithAux` returns is the block compile's**: a
lone non-inductive constant's `compileConstantInfo`, or the mutual block
`compileMutualBlock` compiled from the members' classes, up to the class
order it records (the aux tail and hook 1 run after it and return it as it
is). -/
theorem compileBlockWithAux_result {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {s s' : BlockState} {r : BlockResult} {layout? : Option Ixon.AuxLayout} {pub : Ix.Compile.Pass.Published}
    (h : rawRun (compileBlockWithAux lo all) ctx s = (.ok (r, layout?, pub), s')) :
    ∃ const s₁, rawRun (findConst lo) ctx s = (.ok const, s₁) ∧
      ((∃ s₂, rawRun (compileConstantInfo const) ctx s₁ = (.ok r, s₂)) ∨
        ∃ cs s₂ sorted s₃ out s₄, rawRun (forIn all #[] fun n (acc : Array Ix.MutConst) => do
            match ← findConst n with
            | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
            | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
            | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
            | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
            | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
            | _ => pure (ForInStep.yield acc)) ctx s₁ = (.ok cs, s₂) ∧
          rawRun (sortConsts cs.toList) ctx s₂ = (.ok sorted, s₃) ∧
          rawRun (compileMutualBlock (orderRecursorFamily sorted)) ctx s₃ = (.ok out, s₄) ∧
          recordsOf r = recordsOf out) := by
  unfold compileBlockWithAux at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  refine ⟨const, s₁, hc, ?_⟩
  rcases rawRun_ite h with h | h
  · left
    obtain ⟨result, s₂, hr, h⟩ := bind_ok h
    rw [rawRun_pure] at h
    cases h
    exact ⟨_, hr⟩
  · right
    obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
    obtain ⟨sorted, s₃, hsorted, h⟩ := bind_ok h
    obtain ⟨out, s₄, hout, h⟩ := bind_ok h
    refine ⟨cs, s₂, sorted, s₃, out, s₄, hcs, hsorted, hout, ?_⟩
    revert h
    refine Returns.elim
      (P := fun (x : BlockResult × Option Ixon.AuxLayout × Ix.Compile.Pass.Published) =>
        recordsOf x.1 = recordsOf out) ?_
    repeat (first | (exact Returns.pure rfl) | split | (apply Returns.bind; intro _))


theorem findConst_ok {n : Ix.Name} {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {c : Ix.ConstantInfo}
    (ran : rawRun (findConst n) ctx s = (.ok c, s')) : ctx.1.env.get? n = some c := by
  simp only [findConst, Ix.CompileCert.rawRun_bind, Ix.CompileCert.rawRun_read] at ran
  cases found : ctx.1.env.get? n with
  | none => rw [found] at ran; cases ran
  | some c' => rw [found] at ran; cases ran; rfl

theorem forIn_set_state {γ : Type} {all : Ix.Set Ix.Name} {init : γ} {body : Ix.Name → γ → CompileM (ForInStep γ)}
    {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {x : Except CompileError γ}
    (h : rawRun (forIn all init body) ctx s = (x, s')) (keeps : ∀ n acc, Preserves id (body n acc)) :
    s' = s := by
  have key := Preserves.forIn_list all.toList init body keeps ctx s
  rw [← Std.HashSet.forIn_eq_forIn_toList, h] at key
  exact key

/-- **`compileBlockWithAux_result` from the state it starts in**: the
member lookups and the members' loop change no state, so the block compile
(a lone constant's, or `sortConsts` then `compileMutualBlock`) runs from the
state `compileBlockWithAux` starts from, the empty one in `runBlockWithAux`. -/
theorem compileBlockWithAux_records {ctx : CompileEnv × BlockEnv} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    {s s' : BlockState} {r : BlockResult} {layout? : Option Ixon.AuxLayout} {pub : Ix.Compile.Pass.Published}
    (h : rawRun (compileBlockWithAux lo all) ctx s = (.ok (r, layout?, pub), s')) :
    ∃ const, ctx.1.env.get? lo = some const ∧
      ((∃ s₂, rawRun (compileConstantInfo const) ctx s = (.ok r, s₂)) ∨
        ∃ (cs : Array Ix.MutConst) (out : BlockResult) (s₄ : BlockState),
          rawRun (sortConsts cs.toList >>= fun sorted => compileMutualBlock (orderRecursorFamily sorted)) ctx s =
            (.ok out, s₄) ∧ recordsOf r = recordsOf out) := by
  obtain ⟨const, s₁, hc, rest⟩ := compileBlockWithAux_result h
  have h₁ : s₁ = s := by
    have := findConst_preserves lo ctx s
    rw [hc] at this
    exact this
  subst h₁
  refine ⟨const, findConst_ok hc, ?_⟩
  rcases rest with single | ⟨cs, s₂, sorted, s₃, out, s₄, hcs, hsorted, hout, same⟩
  · exact .inl single
  · have h₂ : s₂ = s₁ := forIn_set_state hcs fun n acc => by
      refine Preserves.bind (findConst_preserves n) fun c => ?_
      split
      · exact Preserves.bind (mkIndc_preserves _) fun _ => Preserves.pure id _
      all_goals exact Preserves.pure id _
    subst h₂
    refine .inr ⟨cs, out, s₄, ?_, same⟩
    rw [Ix.CompileCert.rawRun_bind, hsorted]
    exact hout

/-- **A block hook 2 leaves alone publishes the block compile's records**:
under `prepareBlock`'s identity (`prepareBlock_unreferenced`), the records
`runBlockWithAux` returns are those of the lone constant's
`compileConstantInfo`, or of `sortConsts` then `compileMutualBlock` over the
members, each run from the empty block state in the block's environment. -/
theorem runBlockWithAux_records {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name}
    (prep : Ix.Compile.Pass.prepareBlock cenv all lo = .ok (cenv, {}))
    {r : BlockResult} {cache : BlockState} {layout? : Option Ixon.AuxLayout}
    {pub : Ix.Compile.Pass.Published}
    (h : runBlockWithAux cenv all lo = .ok (r, cache, layout?, pub)) :
    ∃ const, cenv.env.get? lo = some const ∧
      ((∃ (r' : BlockResult) (s₂ : BlockState), rawRun (compileConstantInfo const)
          (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} = (.ok r', s₂) ∧
          recordsOf r = recordsOf r') ∨
        ∃ (cs : Array Ix.MutConst) (out : BlockResult) (s₄ : BlockState),
          rawRun (sortConsts cs.toList >>= fun sorted => compileMutualBlock (orderRecursorFamily sorted))
            (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} = (.ok out, s₄) ∧
          recordsOf r = recordsOf out) := by
  obtain ⟨r', pub', ran, same, -⟩ := runBlockWithAux_unreferenced prep h
  obtain ⟨const, found, rest⟩ := compileBlockWithAux_records (Ix.CompileCert.run_success ran)
  refine ⟨const, found, ?_⟩
  rcases rest with ⟨s₂, single⟩ | ⟨cs, out, s₄, block, same₂⟩
  · exact .inl ⟨r', s₂, single, same⟩
  · exact .inr ⟨cs, out, s₄, block, same.trans same₂⟩

end Ix.Cert.PassHooks
