import Ix.CompileCert.Publication
import Ix.CompileCert.SourceFamilyTraversal
import Ix.CompileCert.HeadWriterFrame
import Ix.CompileCert.Opt.Engine

/-!
Authenticated source image heads through the actual publication hooks, merge,
failed-promotion erasure and optimization lookup. The invariant concerns the
full stored key, not just its cached name digest. It supplies the source-family
construction/closure witness when a derived head is used by an optimization.

The results are local transition contracts. The whole compiler's cache-production
trace, view/memo correspondence and generator semantics remain separate
obligations; this module does not assume or claim the complete unit theorem.
-/

namespace Ix.CompileCert.HeadPublication

open Ix (Name)
open Ix.CompileM Ix.Compile.Pass
open Ix.AuxGen.SourceFamily
open SourceFamilyTraversal
open HeadWriterFrame

abbrev Heads := Std.HashMap Name Name

/-- A derived head's actual source-order recipe and checked dependency set,
bound to the source owner recorded by the driver. -/
def Certified (source : Ix.Environment) (name owner : Name) : Prop :=
  isDerived name = true →
    ∃ all : Array Name, ∃ includeBRecOn : Bool, ∃ recipes : Array Recipe,
      all[0]? = some owner ∧ reconstruct source all includeBRecOn = .ok recipes ∧
      ∃ visited : Array Name, name ∈ visited ∧
        AllChecked { source with overlay := {} } recipes visited ∧
        ∀ member ∈ visited, DependenciesClosed recipes member visited

/-- The property belongs to the full key actually stored in the table,
independently of the digest-equivalence used to find a bucket. -/
def TableValid (source : Ix.Environment) (heads : Heads) : Prop :=
  ∀ query stored owner, heads.getKey? query = some stored → heads[query]? = some owner →
    Certified source stored owner

def ClaimsValid (source : Ix.Environment) (claims : Array (Name × Name)) : Prop :=
  ∀ row ∈ claims, Certified source row.1 row.2

theorem headOwner_source {heads : Heads} {name owner : Name}
    (found : headOwner? heads name = some owner) :
    heads.getKey? name = some name ∧ heads[name]? = some owner := by
  unfold headOwner? at found
  cases key : heads.getKey? name <;> simp only [key, bind, Option.bind] at found
  · contradiction
  rename_i stored
  split at found
  · rename_i same
    have equal := (Ix.Compile.Image.RawExact.nameEq_eq_true _ _).mp same
    subst stored
    exact ⟨rfl, found⟩
  · contradiction

theorem headOwner_certified {source : Ix.Environment} {heads : Heads}
    (valid : TableValid source heads) {name owner : Name}
    (found : headOwner? heads name = some owner) : Certified source name owner := by
  obtain ⟨stored, value⟩ := headOwner_source found
  exact valid name name owner stored value

theorem sourceImageHeads_certified {source : Ix.Environment} {all : Array Name} {name owner : Name}
    (first : all[0]? = some owner) (selected : name ∈ sourceImageHeads source all) :
    Certified source name owner := by
  intro derived
  let candidates := (imageKinds source.get? all).filter
    (Ix.AuxGen.SourceIdentity.permitsOptimization source)
  change name ∈ filterHeads source all candidates at selected
  obtain ⟨recipes, constructed⟩ := SourceFamily.filterHeads_constructed selected derived
  have closure := filterHeads_closed_source selected derived
  rw [constructed] at closure
  exact ⟨all, candidates.any isBRecOn, recipes, first, constructed, closure⟩

theorem claims_of_sourceImageHeads {source : Ix.Environment} {all : Array Name} {owner : Name}
    (first : all[0]? = some owner) :
    ClaimsValid source ((sourceImageHeads source all).map (·, owner)) := by
  rintro row member
  obtain ⟨name, selected, rfl⟩ := Array.mem_map.mp member
  exact sourceImageHeads_certified first selected

theorem claims_append {source : Ix.Environment} {a b : Array (Name × Name)}
    (left : ClaimsValid source a) (right : ClaimsValid source b) : ClaimsValid source (a ++ b) := by
  intro row member
  rcases Array.mem_append.mp member with before | after
  · exact left row before
  · exact right row after

theorem frame_then_claims {source : Ix.Environment} {action : CompileM α}
    {update : BlockState → BlockState} {context : CompileEnv × BlockEnv}
    {before after : BlockState} (framed : Frame action)
    (writes : ∀ state, ClaimsValid source state.p3Heads → ClaimsValid source (update state).p3Heads)
    (valid : ClaimsValid source before.p3Heads)
    (success : rawRun (action >>= fun _ => modifyBlockState update) context before = (.ok (), after)) :
    ClaimsValid source after.p3Heads := by
  rw [rawRun_bind] at success
  have stable := framed context before
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at success stable
    cases outcome with
    | error error => cases congrArg Prod.fst success
    | ok value =>
      dsimp only at success stable
      rw [rawRun_modify] at success
      have equal := congrArg Prod.snd success
      dsimp only at equal
      rw [← equal]
      apply writes middle
      simpa only [stable] using valid

theorem editChangedBlock_claims (cenv : CompileEnv) (benv : BlockEnv)
    (before after : BlockState) (cs : Array Ix.MutConst) (classes : Array (Array Name))
    (layout : Option Ixon.AuxLayout)
    (valid : ClaimsValid cenv.env before.p3Heads)
    (success : CompileM.run cenv benv before (editChangedBlock cs classes layout) = .ok ((), after)) :
    ClaimsValid cenv.env after.p3Heads := by
  have result := run_success success
  simp only [editChangedBlock, rawRun_bind, rawRun_read] at result
  cases inputs : displayInputs cs classes layout with
  | none =>
    simp only [inputs, rawRun_pure, Prod.mk.injEq] at result
    cases result.2
    exact valid
  | some data =>
    rcases data with ⟨all, representative, perm⟩
    simp only [inputs] at result
    cases first : all[0]? with
    | none =>
      simp only [first, rawRun_pure, Prod.mk.injEq] at result
      cases result.2
      exact valid
    | some owner =>
      simp only [first, rawRun_bind] at result
      have stable := Frame.moveToDisplay all representative perm (fun _ => true) (cenv, benv) before
      cases moved : rawRun (moveToDisplay all representative perm (fun _ => true)) (cenv, benv) before with
      | mk outcome middle =>
        rw [moved] at result stable
        cases outcome with
        | error error => cases congrArg Prod.fst result
        | ok display =>
          dsimp only at stable
          simp only [rawRun_modify, Prod.mk.injEq] at result
          cases result.2
          apply claims_append
          · simpa only [stable] using valid
          · exact claims_of_sourceImageHeads first

theorem editPermutedBelowFamily_claims (cenv : CompileEnv) (benv : BlockEnv)
    (before after : BlockState) (cs : Array Ix.MutConst)
    (valid : ClaimsValid cenv.env before.p3Heads)
    (success : CompileM.run cenv benv before (editPermutedBelowFamily cs) = .ok ((), after)) :
    ClaimsValid cenv.env after.p3Heads := by
  have result := run_success success
  simp only [editPermutedBelowFamily, rawRun_bind, rawRun_read] at result
  repeat' first
    | (have equal : before = after := congrArg Prod.snd result
       simpa only [← equal] using valid)
    | (apply frame_then_claims (Frame.moveToDisplay _ _ _ _) ?_ valid result
       intro state checked
       apply claims_append checked
       apply claims_of_sourceImageHeads
       assumption)
    | (simp only [rawRun_bind, rawRun_get] at result)
    | split at result

theorem table_empty (source : Ix.Environment) : TableValid source {} := by
  intro query stored owner key _
  simp at key

theorem table_insert {source : Ix.Environment} {heads : Heads}
    (valid : TableValid source heads) {name owner : Name}
    (authenticated : Certified source name owner) :
    TableValid source (heads.insert name owner) := by
  intro query stored value key found
  rw [Std.HashMap.getKey?_insert] at key
  rw [Std.HashMap.getElem?_insert] at found
  by_cases same : (name == query) = true
  · simp only [same, ↓reduceIte, Option.some.injEq] at key found
    subst stored
    subst value
    exact authenticated
  · simp only [same] at key found
    exact valid query stored value key found

theorem table_fold {source : Ix.Environment} {heads : Heads}
    (valid : TableValid source heads) (claims : List (Name × Name))
    (checked : ∀ row ∈ claims, Certified source row.1 row.2) :
    TableValid source (claims.foldl (fun table row => table.insert row.1 row.2) heads) := by
  induction claims generalizing heads with
  | nil => exact valid
  | cons row rest ih =>
    apply ih (table_insert valid (checked row (by simp)))
    intro later member
    exact checked later (List.mem_cons_of_mem _ member)

theorem table_publish {source : Ix.Environment} {heads : Heads} {claims : Array (Name × Name)}
    (valid : TableValid source heads) (checked : ClaimsValid source claims) :
    TableValid source (claims.foldl (fun table row => table.insert row.1 row.2) heads) := by
  rw [← Array.foldl_toList]
  exact table_fold valid claims.toList (fun row member => checked row (by simpa using member))

theorem table_erase {source : Ix.Environment} {heads : Heads}
    (valid : TableValid source heads) (name : Name) : TableValid source (heads.erase name) := by
  intro query stored owner key found
  rw [Std.HashMap.getKey?_erase] at key
  rw [Std.HashMap.getElem?_erase] at found
  by_cases same : (name == query) = true
  · simp [same] at key
  · simp only [same] at key found
    exact valid query stored owner key found

theorem table_erase_list {source : Ix.Environment} {heads : Heads}
    (valid : TableValid source heads) (names : List Name) :
    TableValid source (names.foldl (fun table name => table.erase name) heads) := by
  induction names generalizing heads with
  | nil => exact valid
  | cons name rest ih => exact ih (table_erase valid name)

def observe (env : CompileEnv) : Ix.Environment × Heads × Bool :=
  (env.env, env.p3Heads, env.pass3)

private theorem named_observe (rows : Array (Name × Ixon.Named)) (initial : CompileEnv) :
    observe (forIn (m := Id) rows initial (fun row state =>
      .yield { state with nameToNamed := state.nameToNamed.insert row.1 row.2 })) =
      observe initial := by
  apply Publication.forIn_preserves <;> intro row state <;> rfl

private theorem aux_observe (rows : Array (Address × Ixon.Constant)) (initial : CompileEnv) :
    observe (forIn (m := Id) rows initial (fun row state =>
      .yield { state with constants := state.constants.insert row.1 (Ixon.ser row.2) })) =
      observe initial := by
  apply Publication.forIn_preserves <;> intro row state <;> rfl

private theorem projection_observe (rows : Array (Name × Ixon.Constant × Ixon.ConstantMeta))
    (initial : CompileEnv) :
    observe (forIn (m := Id) rows initial (fun row state =>
      let bytes := Ixon.ser row.2.1
      let address := Address.blake3 bytes
      .yield { state with
        totalBytes := state.totalBytes + bytes.size
        constants := state.constants.insert address bytes
        nameToNamed := state.nameToNamed.insert row.1 { addr := address, constMeta := row.2.2 }
        nameToAddr := state.nameToAddr.insert row.1 address })) = observe initial := by
  apply Publication.forIn_preserves <;> intro row state <;> rfl

private theorem class_observe (names : Array Name) (classes : Array (Array Name)) (initial : CompileEnv) :
    observe (forIn (m := Id) names initial (fun name state =>
      .yield { state with blocks := state.blocks.insert name classes })) = observe initial := by
  apply Publication.forIn_preserves <;> intro row state <;> rfl

private theorem classes_observe (classes : Array (Array Name)) (initial : CompileEnv) :
    observe (forIn (m := Id) classes initial (fun names state =>
      .yield (forIn (m := Id) names state (fun name state =>
        .yield { state with blocks := state.blocks.insert name classes })))) = observe initial := by
  apply Publication.forIn_preserves
  · intro row state; rfl
  · intro row state
    exact class_observe row classes state

private abbrev namedLoop (rows : Array (Name × Ixon.Named)) (initial : CompileEnv) : CompileEnv :=
  forIn (m := Id) rows initial (fun row state =>
    .yield { state with nameToNamed := state.nameToNamed.insert row.1 row.2 })
private abbrev auxLoop (rows : Array (Address × Ixon.Constant)) (initial : CompileEnv) : CompileEnv :=
  forIn (m := Id) rows initial (fun row state =>
    .yield { state with constants := state.constants.insert row.1 (Ixon.ser row.2) })
private abbrev projectionLoop (rows : Array (Name × Ixon.Constant × Ixon.ConstantMeta))
    (initial : CompileEnv) : CompileEnv :=
  forIn (m := Id) rows initial (fun row state =>
    let bytes := Ixon.ser row.2.1
    let address := Address.blake3 bytes
    .yield { state with
      totalBytes := state.totalBytes + bytes.size
      constants := state.constants.insert address bytes
      nameToNamed := state.nameToNamed.insert row.1 { addr := address, constMeta := row.2.2 }
      nameToAddr := state.nameToAddr.insert row.1 address })

private theorem named_source (rows : Array (Name × Ixon.Named)) (initial : CompileEnv) :
    (namedLoop rows initial).env = initial.env :=
  congrArg Prod.fst (named_observe rows initial)
private theorem named_heads (rows : Array (Name × Ixon.Named)) (initial : CompileEnv) :
    (namedLoop rows initial).p3Heads = initial.p3Heads :=
  congrArg (fun view => view.2.1) (named_observe rows initial)
private theorem named_pass3 (rows : Array (Name × Ixon.Named)) (initial : CompileEnv) :
    (namedLoop rows initial).pass3 = initial.pass3 :=
  congrArg (fun view => view.2.2) (named_observe rows initial)
private theorem aux_source (rows : Array (Address × Ixon.Constant)) (initial : CompileEnv) :
    (auxLoop rows initial).env = initial.env :=
  congrArg Prod.fst (aux_observe rows initial)
private theorem aux_heads (rows : Array (Address × Ixon.Constant)) (initial : CompileEnv) :
    (auxLoop rows initial).p3Heads = initial.p3Heads :=
  congrArg (fun view => view.2.1) (aux_observe rows initial)
private theorem aux_pass3 (rows : Array (Address × Ixon.Constant)) (initial : CompileEnv) :
    (auxLoop rows initial).pass3 = initial.pass3 :=
  congrArg (fun view => view.2.2) (aux_observe rows initial)
private theorem projection_source (rows : Array (Name × Ixon.Constant × Ixon.ConstantMeta)) (initial : CompileEnv) :
    (projectionLoop rows initial).env = initial.env :=
  congrArg Prod.fst (projection_observe rows initial)
private theorem projection_heads (rows : Array (Name × Ixon.Constant × Ixon.ConstantMeta)) (initial : CompileEnv) :
    (projectionLoop rows initial).p3Heads = initial.p3Heads :=
  congrArg (fun view => view.2.1) (projection_observe rows initial)
private theorem projection_pass3 (rows : Array (Name × Ixon.Constant × Ixon.ConstantMeta)) (initial : CompileEnv) :
    (projectionLoop rows initial).pass3 = initial.pass3 :=
  congrArg (fun view => view.2.2) (projection_observe rows initial)

set_option maxRecDepth 2048 in
theorem merge_observe (before : DriverAcc) (lo : Name) (result : BlockResult) (cache : BlockState) :
    observe (mergeCompiledBlock before lo result cache).cenv =
      (before.cenv.env,
        if before.cenv.pass3 then
          cache.p3Heads.foldl (fun heads row => heads.insert row.1 row.2) before.cenv.p3Heads
        else before.cenv.p3Heads,
        before.cenv.pass3) := by
  unfold mergeCompiledBlock
  simp only [Id.run, bind, pure]
  split
  all_goals try simp only [named_source, named_heads, named_pass3,
    aux_source, aux_heads, aux_pass3, projection_source, projection_heads, projection_pass3]
  all_goals split <;> split
  all_goals simp only [classes_observe]
  all_goals simp_all [observe]

theorem merge_source (before : DriverAcc) (lo : Name) (result : BlockResult) (cache : BlockState) :
    (mergeCompiledBlock before lo result cache).cenv.env = before.cenv.env := by
  exact congrArg Prod.fst (merge_observe before lo result cache)

theorem merge_heads (before : DriverAcc) (lo : Name) (result : BlockResult) (cache : BlockState) :
    (mergeCompiledBlock before lo result cache).cenv.p3Heads =
      if before.cenv.pass3 then
        cache.p3Heads.foldl (fun heads row => heads.insert row.1 row.2) before.cenv.p3Heads
      else before.cenv.p3Heads := by
  exact congrArg (fun view => view.2.1) (merge_observe before lo result cache)

theorem merge_valid (before : DriverAcc) (lo : Name) (result : BlockResult) (cache : BlockState)
    (valid : TableValid before.cenv.env before.cenv.p3Heads)
    (checked : ClaimsValid before.cenv.env cache.p3Heads) :
    TableValid (mergeCompiledBlock before lo result cache).cenv.env
      (mergeCompiledBlock before lo result cache).cenv.p3Heads := by
  rw [merge_source, merge_heads]
  split
  · exact table_publish valid checked
  · exact valid

theorem merge_lookup_certified (before : DriverAcc) (lo : Name) (result : BlockResult) (cache : BlockState)
    (valid : TableValid before.cenv.env before.cenv.p3Heads)
    (checked : ClaimsValid before.cenv.env cache.p3Heads) {name owner : Name}
    (found : headOwner? (mergeCompiledBlock before lo result cache).cenv.p3Heads name = some owner) :
    Certified before.cenv.env name owner := by
  have preserved := headOwner_certified (merge_valid before lo result cache valid checked) found
  rwa [merge_source] at preserved

theorem forIn_project_list {α β γ : Type} (items : List α) (initial : β)
    (body : α → β → Id (ForInStep β)) (project : β → γ) (next : γ → α → γ)
    (continues : ∀ item state, body item state = .yield (body item state).value)
    (commutes : ∀ item state, project (body item state).value = next (project state) item) :
    project (forIn (m := Id) items initial body) = items.foldl next (project initial) := by
  rw [Canon.forIn_id_list body continues]
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.foldl_cons, ih, commutes]

private theorem erase_observe (names : List Name) (view : Ix.Environment × Heads × Bool) :
    names.foldl (fun prior name => (prior.1, prior.2.1.erase name, prior.2.2)) view =
      (view.1, names.foldl (fun heads name => heads.erase name) view.2.1, view.2.2) := by
  induction names generalizing view with
  | nil => rfl
  | cons name rest ih => exact ih _

set_option maxRecDepth 2048 in
theorem failAuxPromotion_observe (before : DriverAcc) (all : Ix.Set Name) (message : String) :
    observe (failAuxPromotion before all message).cenv =
      (before.cenv.env, all.toList.foldl (fun heads name => heads.erase name) before.cenv.p3Heads,
        before.cenv.pass3) := by
  unfold failAuxPromotion
  simp only [Id.run, bind, pure]
  rw [Std.HashSet.forIn_eq_forIn_toList]
  rw [forIn_project_list all.toList before _ (fun state => observe state.cenv)
    (fun view name => (view.1, view.2.1.erase name, view.2.2))
    (fun _ _ => rfl) (fun _ _ => rfl)]
  exact erase_observe _ _

theorem failAuxPromotion_valid (before : DriverAcc) (all : Ix.Set Name) (message : String)
    (valid : TableValid before.cenv.env before.cenv.p3Heads) :
    TableValid (failAuxPromotion before all message).cenv.env
      (failAuxPromotion before all message).cenv.p3Heads := by
  have source := congrArg Prod.fst (failAuxPromotion_observe before all message)
  have heads := congrArg (fun view => view.2.1) (failAuxPromotion_observe before all message)
  dsimp only [observe] at source heads
  rw [source, heads]
  exact table_erase_list valid all.toList

set_option maxHeartbeats 2000000 in
theorem no_block_small (env : Ix.Compile.Pass.Opt.OptEnv) (o : Ix.Compile.Pass.Opt.Occ)
    (recur : Ix.Compile.Pass.Opt.Occ → Option Ix.Expr) (missing : env.blockOf o.head = none) :
    Ix.Compile.Pass.Opt.O1.apply env o = none ∧
    Ix.Compile.Pass.Opt.O2.apply recur env o = none ∧
    Ix.Compile.Pass.Opt.O3.apply env o = none ∧
    Ix.Compile.Pass.Opt.O4.apply env o = none ∧
    Ix.Compile.Pass.Opt.O6.apply env o = none ∧
    Ix.Compile.Pass.Opt.O7.apply env o = none ∧
    Ix.Compile.Pass.Opt.O8.apply env o = none ∧
    Ix.Compile.Pass.Opt.O9.apply env o = none ∧
    Ix.Compile.Pass.Opt.readCollapseRec env o = none := by
  cases classified : Ix.Compile.Pass.Opt.classify o.head with
  | none =>
    simp [Ix.Compile.Pass.Opt.O1.apply, Ix.Compile.Pass.Opt.O2.apply,
      Ix.Compile.Pass.Opt.O3.apply, Ix.Compile.Pass.Opt.O4.apply,
      Ix.Compile.Pass.Opt.O6.apply, Ix.Compile.Pass.Opt.O7.apply,
      Ix.Compile.Pass.Opt.O8.apply, Ix.Compile.Pass.Opt.O9.apply,
      Ix.Compile.Pass.Opt.readCollapseRec, classified]
  | some pair =>
    rcases pair with ⟨kind, recursor⟩
    cases kind <;> simp [Ix.Compile.Pass.Opt.O1.apply, Ix.Compile.Pass.Opt.O2.apply,
      Ix.Compile.Pass.Opt.O3.apply, Ix.Compile.Pass.Opt.O4.apply,
      Ix.Compile.Pass.Opt.O6.apply, Ix.Compile.Pass.Opt.O7.apply,
      Ix.Compile.Pass.Opt.O8.apply, Ix.Compile.Pass.Opt.O9.apply,
      Ix.Compile.Pass.Opt.readCollapseRec, classified, missing]

set_option maxHeartbeats 500000 in
theorem no_block_o11a (env : Ix.Compile.Pass.Opt.OptEnv) (o : Ix.Compile.Pass.Opt.Occ)
    (missing : env.blockOf o.head = none) : Ix.Compile.Pass.Opt.O11a.apply env o = none := by
  cases classified : Ix.Compile.Pass.Opt.classify o.head with
  | none =>
    simp [Ix.Compile.Pass.Opt.O11a.apply, Ix.Compile.Pass.Opt.O11a.applyWith,
      Ix.Compile.Pass.Opt.O11a.applyWithE, Ix.Compile.Pass.Opt.O11aM.pattern,
      classified, bind, Except.bind, Except.toOption, throw, throwThe, MonadExceptOf.throw]
  | some pair =>
    rcases pair with ⟨kind, recursor⟩
    cases kind <;> simp [Ix.Compile.Pass.Opt.O11a.apply, Ix.Compile.Pass.Opt.O11a.applyWith,
      Ix.Compile.Pass.Opt.O11a.applyWithE, Ix.Compile.Pass.Opt.O11aM.pattern,
      classified, missing, bind, Except.bind, pure, Except.pure, Except.toOption, throw, throwThe, MonadExceptOf.throw]

theorem engineN_no_block (fuel : Nat) (env : Ix.Compile.Pass.Opt.OptEnv)
    (o : Ix.Compile.Pass.Opt.Occ) (missing : env.blockOf o.head = none) :
    Ix.Compile.Pass.Opt.engineN fuel env o = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    obtain ⟨h1, h2, h3, h4, h6, h7, h8, _, _⟩ := no_block_small env o
      (fun next => (Ix.Compile.Pass.Opt.engineN fuel env next).map (·.2)) missing
    have h11 := no_block_o11a env o missing
    simp [Ix.Compile.Pass.Opt.engineN, Ix.Compile.Pass.Opt.passes,
      Ix.Compile.Pass.Opt.pjPasses, h1, h2, h3, h4, h6, h7, h8, h11]

theorem engineFull_no_block (env : Ix.Compile.Pass.Opt.OptEnv) (o : Ix.Compile.Pass.Opt.Occ)
    (missing : env.blockOf o.head = none) : Ix.Compile.Pass.Opt.engineFull env o = none := by
  obtain ⟨_, _, _, _, _, _, _, h9, collapsed⟩ := no_block_small env o (fun _ => none) missing
  simp [Ix.Compile.Pass.Opt.engineFull, Ix.Compile.Pass.Opt.engine,
    engineN_no_block 64 env o missing, Ix.Compile.Pass.Opt.emitPasses, h9,
    Ix.Compile.Pass.Opt.O10.apply, Ix.Compile.Pass.Opt.O12.apply, collapsed]

theorem engineFull_block {env : Ix.Compile.Pass.Opt.OptEnv} {o : Ix.Compile.Pass.Opt.Occ}
    {result : String × Ix.Expr × Array Ix.ConstantInfo}
    (hit : Ix.Compile.Pass.Opt.engineFull env o = some result) :
    ∃ block, env.blockOf o.head = some block := by
  cases found : env.blockOf o.head with
  | none => rw [engineFull_no_block env o found] at hit; contradiction
  | some block => exact ⟨block, rfl⟩

theorem optLookup_certified (cenv : CompileEnv) (blocks : Std.HashMap Name Ix.Compile.Pass.Opt.OptBlock)
    (valid : TableValid cenv.env cenv.p3Heads)
    {site : Option Name} {name : Name} {levels : Array Ix.Level} {args : Array Ix.Expr}
    {result : Ix.Expr × Array Ix.ConstantInfo × Option String}
    (hit : optLookup cenv blocks site name levels args = some result) :
    ∃ owner, headOwner? cenv.p3Heads name = some owner ∧ Certified cenv.env name owner := by
  unfold optLookup at hit
  split at hit
  · contradiction
  · obtain ⟨output, engine, _⟩ := Ix.CompileCert.Opt.omap_some hit
    obtain ⟨block, selected⟩ := engineFull_block engine
    change (headOwner? cenv.p3Heads name).bind blocks.get? = some block at selected
    cases owner : headOwner? cenv.p3Heads name with
    | none => simp [owner] at selected
    | some key => exact ⟨key, rfl, headOwner_certified valid owner⟩

/-- One actual changed-block publication step, with its local writer proof
discharging the new-claims premise of the merge invariant. -/
theorem changed_block_lookup_certified (before : DriverAcc) (benv : BlockEnv)
    (initial final : BlockState) (cs : Array Ix.MutConst) (classes : Array (Array Name))
    (layout : Option Ixon.AuxLayout) (lo : Name) (result : BlockResult)
    (prior : TableValid before.cenv.env before.cenv.p3Heads)
    (localPrior : ClaimsValid before.cenv.env initial.p3Heads)
    (written : CompileM.run before.cenv benv initial (editChangedBlock cs classes layout) = .ok ((), final))
    {name owner : Name}
    (found : headOwner? (mergeCompiledBlock before lo result final).cenv.p3Heads name = some owner) :
    Certified before.cenv.env name owner :=
  merge_lookup_certified before lo result final prior
    (editChangedBlock_claims before.cenv benv initial final cs classes layout localPrior written) found

/-- The corresponding publication step for a permuted Prop below family. -/
theorem permuted_below_lookup_certified (before : DriverAcc) (benv : BlockEnv)
    (initial final : BlockState) (cs : Array Ix.MutConst) (lo : Name) (result : BlockResult)
    (prior : TableValid before.cenv.env before.cenv.p3Heads)
    (localPrior : ClaimsValid before.cenv.env initial.p3Heads)
    (written : CompileM.run before.cenv benv initial (editPermutedBelowFamily cs) = .ok ((), final))
    {name owner : Name}
    (found : headOwner? (mergeCompiledBlock before lo result final).cenv.p3Heads name = some owner) :
    Certified before.cenv.env name owner :=
  merge_lookup_certified before lo result final prior
    (editPermutedBelowFamily_claims before.cenv benv initial final cs localPrior written) found

theorem claims_empty (source : Ix.Environment) : ClaimsValid source #[] := by
  intro row member
  simp at member

end Ix.CompileCert.HeadPublication
