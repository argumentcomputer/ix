import Ix.Cert.TraceSegments
import Ix.Cert.FamilyGroups
import Ix.Cert.LeanOrder

/-! # A group's compile runs as the group, in Lean's order

The fold compiles every block of the input's condensation with `runBlock`. A block of one
constant that is no inductive or constructor compiles alone; any other runs its members' loop
and compiles the loop's members in Lean's order (`runBlock_paths`). This module shows that the
block of each of quotient Source's groups runs as the group, in the group's own order, in the
forms the reader's segment theorems take (`TraceSegments`):

* the members' loop makes one member per name of the block (`membersLoop_eq`, `memberOf`);
* `FoldBlock` packages what the fold gives about the block of a closure name (`foldBlock_of`):
  its run, its publication, its snapshot's environment, freshness, resolution and blobs;
* a definitions group of two or more runs `compileMutualBlock` over its definitions in its own
  order (`definitions_run`). Both orders are Lean's (`LeanOrder.sourceClasses_eq`); two members
  of a block never tie, since names that differ only in their hash fields have one key and so one
  published address (`addr_of_key`), while a block's members are published apart
  (`BlockPublication.apart`);
* an inductive group's types run `compileMutualBlock` over the group's members (`types_run`),
  each at its position in its block;
* its recursors run as a family in `blockRecursors`' order, or alone under their own name when
  there is one (`recursors_run`): each recursor sits at its declared position in the family,
  `X.rec` at `X`'s and `first.rec_j` after the block (`recursorFamilyPosition`, with the decimal
  digits of `j` read back).

The types' and recursors' positions need the group's members to have distinct names (a premise,
`Canon.KeysDistinct`), and their blocks need the compile report's family check
(`FamilyBlocks`, `familyBlocks`). `definitions_compiled`, `types_compiled` and `recursors_family`
state the results as `TraceSegments.BlockCompiled`'s and `InductiveCompiled`'s run fields. -/

namespace Ix.Cert.GroupRuns

open Ix.CompileM Ix.CompileCert Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.LeanIngress (Group groupsOf componentGroup isFamily isDefinition blockRecursors)
open Ix.Cert.ClosureLayout (addrOf quotientGraph)
open Ix.Cert.InductiveCompile (indsOf indOf)
open Ix.Cert.LeanOrder (classKey)

/-! ## The block compile's two paths -/

/-- Whether a block's key constant makes the block an inductive block (`compileBlock`'s test). -/
def isIndConst : Ix.ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ => true
  | _ => false

theorem rawRun_ite_cond {α : Type} {c : Prop} [Decidable c] {a b : CompileM α} {ctx : CompileEnv × BlockEnv}
    {s : BlockState} {r : Except CompileError α × BlockState}
    (h : rawRun (if c then a else b) ctx s = r) : (c ∧ rawRun a ctx s = r) ∨ (¬c ∧ rawRun b ctx s = r) := by
  by_cases hc : c
  · exact .inl ⟨hc, by simpa [hc] using h⟩
  · exact .inr ⟨hc, by simpa [hc] using h⟩

/-! ## Blobs the block compile's tail keeps -/

/-- **Every successful run keeps every blob the block reads**, with the bytes it read. -/
def Grows {α : Type} (m : CompileM α) : Prop :=
  ∀ (ctx : CompileEnv × BlockEnv) (s : BlockState) (x : α) (s' : BlockState),
    rawRun m ctx s = (.ok x, s') → BlobWrites.Extends ctx.1.blobs s s'

theorem Grows.elim {α : Type} {m : CompileM α} (hm : Grows m) {ctx : CompileEnv × BlockEnv} {s s' : BlockState}
    {x : α} : rawRun m ctx s = (.ok x, s') → BlobWrites.Extends ctx.1.blobs s s' :=
  hm ctx s x s'

theorem Grows.pure {α : Type} (x : α) : Grows (Pure.pure x : CompileM α) := by
  intro ctx s y s' ran
  rw [rawRun_pure] at ran
  cases ran
  exact .refl _ _

theorem Grows.throw {α : Type} (e : CompileError) : Grows (throw e : CompileM α) := by
  intro ctx s y s' ran
  rw [rawRun_throw] at ran
  cases ran

theorem Grows.bind {α β : Type} {m : CompileM β} {k : β → CompileM α} (hm : Grows m) (hk : ∀ b, Grows (k b)) :
    Grows (m >>= k) := by
  intro ctx s x s' ran
  obtain ⟨b, mid, h₁, h₂⟩ := bind_ok ran
  exact (hm ctx s b mid h₁).trans (hk b ctx mid x s' h₂)

theorem Grows.ite {α : Type} {c : Prop} [Decidable c] {a b : CompileM α} (ha : Grows a) (hb : Grows b) :
    Grows (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem Grows.modify {f : BlockState → BlockState} (h : ∀ s, (f s).blockBlobs = s.blockBlobs) :
    Grows (modifyBlockState f) := by
  intro ctx s x s' ran
  rw [rawRun_modify] at ran
  cases ran
  exact RefTables.Extends.of_blobs (h s)

theorem Grows.compileName (n : Ix.Name) : Grows (compileName n) := by
  intro ctx s x s' ran
  have := (BlobWrites.compileName_preserves n ctx s).2
  rw [ran] at this
  exact this

theorem Grows.forIn_list {α β : Type} (items : List α) (init : β) (body : α → β → CompileM (ForInStep β))
    (h : ∀ a b, Grows (body a b)) : Grows (forIn items init body) := by
  induction items generalizing init with
  | nil => exact Grows.pure init
  | cons a rest ih =>
    rw [List.forIn_cons]
    refine Grows.bind (h a init) fun r => ?_
    cases r with
    | done v => exact Grows.pure v
    | yield v => exact ih v

theorem Grows.forIn_array {α β : Type} (items : Array α) (init : β) (body : α → β → CompileM (ForInStep β))
    (h : ∀ a b, Grows (body a b)) : Grows (forIn items init body) := by
  rw [← Array.forIn_toList]
  exact Grows.forIn_list items.toList init body h

/-- One step of a walk through a `do` block for `Grows`, as `BlockRecords`' `returns_step` walks
one for `Returns`: a bind (both halves), an `if`, a `return`, a loop over an array, a write that
keeps the blobs, a name's compile, a refusal, or a match on a local. -/
local macro "grows_step" : tactic => `(tactic| first
  | (with_reducible apply Grows.bind)
  | (with_reducible apply Grows.ite)
  | (with_reducible apply Grows.pure)
  | (with_reducible apply Grows.throw)
  | (with_reducible apply Grows.compileName)
  | (with_reducible apply Grows.forIn_array)
  | ((with_reducible apply Grows.modify); intro _; rfl)
  | split
  | ((with_reducible show ∀ _, _); intro _))

theorem registerMutsEntry_grows (cls : List (List MutConst)) (addr : Address) :
    Grows (registerMutsEntry cls addr) := by
  unfold registerMutsEntry
  repeat grows_step

/-- **A block runs on one of its two paths, by its size and its key's kind**: a lone constant
that is no inductive or constructor compiles alone (`compileConstantInfo`), to `runBlock`'s final
state; any other block runs its members' loop from the empty state, and compiles the members in
Lean's order (`compileMutualBlock (sourceClasses cs)`) with the records `runBlock` returns, to a
state whose blobs `runBlock`'s final state keeps (the registrations only add names). -/
theorem runBlock_paths {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {cache : BlockState} (h : runBlock cenv all lo = .ok (r, cache)) :
    ∃ const, cenv.env.get? lo = some const ∧
      (((all.size == 1 && !isIndConst const) = true ∧
          rawRun (compileConstantInfo const) (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} =
            (.ok r, cache)) ∨
        ((all.size == 1 && !isIndConst const) = false ∧ ∃ cs out s₄,
          rawRun (GroupBlocks.membersLoop all.toList #[])
            (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} = (.ok cs, {}) ∧
          rawRun (compileMutualBlock (sourceClasses cs))
            (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {} = (.ok out, s₄) ∧
          BlobWrites.Extends cenv.blobs s₄ cache ∧
          BlockRecords.recordsOf r = BlockRecords.recordsOf out)) := by
  have h' := run_success (BlockRecords.runBlock_compiles h)
  unfold compileBlock at h'
  obtain ⟨const, s₁, hc, h'⟩ := bind_ok h'
  have h₁ : s₁ = {} := by
    have := BlockRecords.findConst_preserves lo (cenv, { all, current := lo, mutCtx := default, univCtx := [] }) {}
    rw [hc] at this
    exact this
  subst h₁
  refine ⟨const, BlockRecords.findConst_ok hc, ?_⟩
  rcases rawRun_ite_cond h' with ⟨hcond, hs⟩ | ⟨hcond, hm⟩
  · exact .inl ⟨hcond, hs⟩
  · right
    refine ⟨Bool.eq_false_iff.mpr hcond, ?_⟩
    obtain ⟨cs, s₂, hcs, hm₁⟩ := bind_ok hm
    obtain ⟨out, s₄, hout, hm₂⟩ := bind_ok hm₁
    have h₂ : s₂ = {} := BlockRecords.forIn_set_state hcs fun n acc => by
      refine Preserves.bind (BlockRecords.findConst_preserves n) fun c => ?_
      split
      · exact Preserves.bind (BlockRecords.mkIndc_preserves _) fun _ => Preserves.pure id _
      all_goals exact Preserves.pure id _
    subst h₂
    refine ⟨cs, out, s₄, ?_, hout, ?_, ?_⟩
    · rw [Std.HashSet.forIn_eq_forIn_toList] at hcs
      exact hcs
    · revert hm₂
      refine Grows.elim ?_
      repeat first
        | exact registerMutsEntry_grows _ _
        | grows_step
    · revert hm₂
      refine BlockRecords.Returns.elim
        (P := fun (x : BlockResult) => BlockRecords.recordsOf x = BlockRecords.recordsOf out) ?_
      repeat returns_step

/-! ## The members' loop -/

/-- A constructor, looked up. -/
def ctorOf (E : Ix.Name → Option Ix.ConstantInfo) (c : Ix.Name) : Option Ix.ConstructorVal :=
  match E c with
  | some (.ctorInfo cv) => some cv
  | _ => none

/-- **The member the block's loop makes of a name**: its constant's, an inductive with the
constructors it lists, looked up; nothing for a constructor, an axiom or a quotient. -/
def memberOf (E : Ix.Name → Option Ix.ConstantInfo) (n : Ix.Name) : Option MutConst :=
  match E n with
  | some (.inductInfo v) => (v.ctors.toList.mapM (ctorOf E)).map fun cs => .indc (indOf v cs.toArray)
  | some (.defnInfo v) => some (MutConst.fromDefinitionVal v)
  | some (.opaqueInfo v) => some (MutConst.fromOpaqueVal v)
  | some (.thmInfo v) => some (MutConst.fromTheoremVal v)
  | some (.recInfo v) => some (.recr v)
  | _ => none

theorem collect_ok {ctx : CompileEnv × BlockEnv} :
    ∀ (names : List Ix.Name) (acc : Array Ix.ConstructorVal) {s s' : BlockState} {out : Array Ix.ConstructorVal},
      rawRun (collectMutConstConstructors names acc) ctx s = (.ok out, s') →
        ∃ cs, names.mapM (ctorOf (ctx.1.env.get? ·)) = some cs ∧ out = acc ++ cs.toArray
  | [], acc, s, s', out, h => by
    simp only [collectMutConstConstructors, rawRun_pure] at h
    cases h
    exact ⟨[], rfl, by simp⟩
  | n :: rest, acc, s, s', out, h => by
    simp only [collectMutConstConstructors] at h
    obtain ⟨c, mid, hc, h⟩ := bind_ok h
    have hfound := BlockRecords.findConst_ok hc
    cases c with
    | ctorInfo cv =>
      obtain ⟨cs, hcs, rfl⟩ := collect_ok rest (acc.push cv) h
      refine ⟨cv :: cs, ?_, by simp⟩
      simp [List.mapM_cons, ctorOf, hfound, hcs]
    | _ => simp [rawRun_throw] at h

/-- **The members' loop makes `memberOf` of each name, in order.** -/
theorem membersLoop_eq {ctx : CompileEnv × BlockEnv} :
    ∀ (l : List Ix.Name) (init : Array MutConst) {s s' : BlockState} {cs : Array MutConst},
      rawRun (GroupBlocks.membersLoop l init) ctx s = (.ok cs, s') →
        cs.toList = init.toList ++ l.filterMap (memberOf (ctx.1.env.get? ·))
  | [], init, s, s', cs, h => by
    unfold GroupBlocks.membersLoop at h
    rw [List.forIn_nil, rawRun_pure] at h
    cases h
    simp
  | k :: l, init, s, s', cs, h => by
    unfold GroupBlocks.membersLoop at h
    rw [List.forIn_cons] at h
    obtain ⟨st, mid, hb, h⟩ := bind_ok h
    obtain ⟨c, mid₀, hc, hb⟩ := bind_ok hb
    have hfound := BlockRecords.findConst_ok hc
    have step : ∃ acc', st = .yield acc' ∧
        acc'.toList = init.toList ++ (memberOf (ctx.1.env.get? ·) k).toList := by
      cases c with
      | inductInfo val =>
        obtain ⟨y, mid', hy, hb⟩ := bind_ok hb
        rw [rawRun_pure] at hb
        cases hb
        unfold MutConst.mkIndc at hy
        obtain ⟨ctors, mid'', hcol, hy⟩ := bind_ok hy
        rw [rawRun_pure] at hy
        cases hy
        obtain ⟨cs', hcs', rfl⟩ := collect_ok _ _ hcol
        refine ⟨_, rfl, ?_⟩
        simp [memberOf, hfound, hcs', indOf]
      | defnInfo val =>
        rw [rawRun_pure] at hb
        cases hb
        exact ⟨_, rfl, by simp [memberOf, hfound]⟩
      | opaqueInfo val =>
        rw [rawRun_pure] at hb
        cases hb
        exact ⟨_, rfl, by simp [memberOf, hfound]⟩
      | thmInfo val =>
        rw [rawRun_pure] at hb
        cases hb
        exact ⟨_, rfl, by simp [memberOf, hfound]⟩
      | recInfo val =>
        rw [rawRun_pure] at hb
        cases hb
        exact ⟨_, rfl, by simp [memberOf, hfound]⟩
      | _ =>
        rw [rawRun_pure] at hb
        cases hb
        exact ⟨_, rfl, by simp [memberOf, hfound]⟩
    obtain ⟨acc', rfl, hacc⟩ := step
    have ih := membersLoop_eq l acc' h
    rw [ih, hacc, List.filterMap_cons]
    cases memberOf (ctx.1.env.get? ·) k <;> simp

/-- A member's name is the name it was made of, up to `==`. -/
theorem memberOf_name {E : Ix.Name → Option Ix.ConstantInfo}
    (named : ∀ k ci, E k = some ci → (ci.getCnst.name == k) = true) {n : Ix.Name} {m : MutConst}
    (h : memberOf E n = some m) : (m.name == n) = true := by
  unfold memberOf at h
  split at h
  · rename_i v hv
    obtain ⟨cs, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact named n _ hv
  all_goals first
    | (rename_i v hv; cases h; exact named n _ hv)
    | cases h

/-- `memberOf` reads its name up to `==`. -/
theorem memberOf_congr {E : Ix.Name → Option Ix.ConstantInfo} (congr : ∀ a b, (a == b) = true → E a = E b)
    {a b : Ix.Name} (h : (a == b) = true) : memberOf E a = memberOf E b := by
  unfold memberOf
  rw [congr a b h]

/-- The loop's members of a set of names are distinct. -/
theorem filterMap_nodup {β : Type} {l : List Ix.Name} {f : Ix.Name → Option β}
    (hl : l.Pairwise fun a b => (a == b) = false)
    (key : ∀ a b x, f a = some x → f b = some x → (a == b) = true) : (l.filterMap f).Nodup :=
  hl.filterMap f fun a a' h b hb b' hb' e => by
    subst e
    rw [key a a' b hb hb'] at h
    cases h

/-! ## The fold's block of a closure name -/

/-- **What the fold gives about a block it compiled**: the fold's run and the state `snap` it
compiled the block at, the block of the input's condensation, the state's environment reading the
input's constants, members in the closure, the block's run and publication, its members unbound
at `snap`, every closure name `snap` resolves published there, and every blob the run reads kept
in the artifact with the bytes it read. -/
structure FoldBlock (env sub : Ix.Environment) (ixe : Ixon.Env) (failures : Failures) (snap : DriverAcc)
    (rep : Ix.Name) (all : Ix.Set Ix.Name) (r : BlockResult) (c : BlockState) : Prop where
  fold : ∃ (cenv cenv₀ : CompileEnv) (sched : FoldSchedule), compileUnchecked env = .ok (ixe, failures, cenv) ∧
    FoldRun { consts := env.consts } (CompiledRefs.envBlocks env) cenv cenv₀ sched ∧
    OnRun (CompiledRefs.envBlocks env) sched (FoldState.init cenv₀ (CompiledRefs.envBlocks env) sched) snap ∧
    Mono snap.cenv cenv
  block : (CompiledRefs.envBlocks env).blocks.get? rep = some all
  env : ∀ x, snap.cenv.env.get? x = env.consts.get? x
  members : LayoutExtra.MembersIn sub all
  ran : runBlock snap.cenv all (blockKey rep all) = .ok (r, c)
  published : BlockPublication.Published ixe sub (blockKey rep all) r
  fresh : ∀ x, all.contains x = true → snap.cenv.nameToAddr.get? x = none
  resolved : ∀ (n : Ix.Name) (a : Address), (sub.consts.get? n).isSome = true →
    snap.cenv.nameToAddr.get? n = some a → (ixe.named.get? n).map (·.addr) = some a
  blobs : ∀ (a : Address) (v : ByteArray), BlobWrites.readBlob snap.cenv.blobs c a = some v →
    ixe.blobs.get? a = some v

/-- **A closure name's published record is a claim of a block the fold compiled**, and the block
is a `FoldBlock`; a name that is no constructor is a member of it. -/
theorem foldBlock_of {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {m : Ix.Name} {ci : Ix.ConstantInfo}
    (hm : (m, ci) ∈ sub.consts.toList) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      (∃ a b, (m, a, b) ∈ claimWrites (blockKey rep all) r) ∧
      ((∀ cv, ci ≠ .ctorInfo cv) → all.contains m = true) := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨cenv, blocks, cenv₀, sched, hu, hblocks, hrun, hpub, owned⟩ :=
    Ix.Cert.compileReport_owned_blobs P.compiled hcl P.none
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hm
  have hmE := SourceStoredNames.stored_input P hm
  have hin : env.consts.contains m = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
      SourceStoredNames.stored_get hmE]
    rfl
  have hn := LayoutExtra.published_resolved P.compiled hu hmem hget hin
  have hs : (sub.consts.get? m).isSome = true := by
    rw [SourceStoredNames.stored_get hm]
    rfl
  obtain ⟨-, snap, rep, all, r, c, b, hsnap, hall, hmono, hsub, hr, hclaim, -, -, hfresh, hblock, hclaims,
    hblobs⟩ := owned m named.addr hn hs
  have hrun' := hrun
  obtain ⟨-, -, henv, -⟩ := hrun'
  have hE : ∀ x, snap.cenv.env.get? x = env.consts.get? x := fun x => by
    rw [reach_env (onRun_reach hsnap), henv, ClosureClaims.view_get, ClosureClaims.input_get]
  subst hblocks
  refine ⟨snap, rep, all, r, c,
    ⟨⟨cenv, cenv₀, sched, hu, hrun, hsnap, hmono⟩, hall, hE, hsub, hr, ⟨hblock, hclaims⟩, hfresh,
      hpub snap hsnap, fun a v h => (hblobs a v h).2⟩, ⟨named.addr, b, hclaim⟩, fun notCtor => ?_⟩
  exact GroupBlocks.claim_member P.compiled hE (blockKey_mem (Condense.condense_nonempty hall)) hr hclaim
    fun cv h => notCtor cv (Option.some.inj ((SourceStoredNames.stored_get hmE).symm.trans h))

/-! ## Names of one key -/

/-- **Two closure names with one ingress key are published at one address**: the address the
artifact gives their common quotient key (`ReadingKeys.keyAddress_quotientKey`). -/
theorem addr_of_key {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {n n' : Ix.Name} {ci ci' : Ix.ConstantInfo}
    (hn : (n, ci) ∈ sub.consts.toList) (hn' : (n', ci') ∈ sub.consts.toList)
    (key : Ix.LeanIngress.ingressKey n = Ix.LeanIngress.ingressKey n') : addrOf ixe n = addrOf ixe n' := by
  obtain ⟨named, hm, hget⟩ := SourceStoredNames.stored_published P hn
  obtain ⟨named', hm', hget'⟩ := SourceStoredNames.stored_published P hn'
  have e₁ := ReadingKeys.keyAddress_quotientKey (defaultTable_check P.table) P.bound P.agree hm
  have e₂ := ReadingKeys.keyAddress_quotientKey (defaultTable_check P.table) P.bound P.agree hm'
  have hq : quotientKey ixe t n = quotientKey ixe t n' := by
    unfold quotientKey
    rw [key]
  rw [hq, e₂] at e₁
  unfold addrOf
  rw [hget, hget', Option.map_some, Option.map_some, e₁]

/-- Names `leanCmp` ties have one ingress key. -/
theorem key_of_tie {a b : Ix.Name} (h : Ix.Name.leanCmp a b = .eq) :
    Ix.LeanIngress.ingressKey a = Ix.LeanIngress.ingressKey b := by
  unfold Ix.LeanIngress.ingressKey
  rw [LeanOrder.ingressName_of_eq a b h]

/-! ## Members at their positions -/

/-- **Members listed at their positions are sorted, distinct and never tie.** -/
theorem positioned {xs : List MutConst} (pos : ∀ i (hi : i < xs.length), (classKey xs[i]).1 = i) :
    xs.Nodup ∧ (xs.Pairwise fun a b => Ix.sourceOrderLt (classKey b) (classKey a) = false) ∧
      ∀ a ∈ xs, ∀ b ∈ xs, Ix.sourceOrderLt (classKey a) (classKey b) = false →
        Ix.sourceOrderLt (classKey b) (classKey a) = false → a = b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij e
    have := pos i hi
    rw [e, pos j hj] at this
    omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    unfold Ix.sourceOrderLt
    rw [pos i hi, pos j hj]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, Bool.and_eq_false_iff]
    exact ⟨by omega, .inl (by simp; omega)⟩
  · intro a ha b hb h₁ h₂
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    have e := (LeanOrder.tie_of_not_lt h₁ h₂).1
    rw [pos i hi, pos j hj] at e
    subst e
    rfl

/-! ## Sets of names -/

/-- A name a set holds is `==` to one of its listed names. -/
theorem listed {all : Ix.Set Ix.Name} {k : Ix.Name} (hk : all.contains k = true) :
    ∃ k' ∈ all.toList, (k == k') = true :=
  List.contains_iff_exists_mem_beq.mp (by rw [Std.HashSet.contains_toList]; exact hk)

/-- A listed name is held. -/
theorem contains_of_listed {all : Ix.Set Ix.Name} {k : Ix.Name} (hk : k ∈ all.toList) : all.contains k = true :=
  Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hk)

/-- Two names a set of one element holds are `==`. -/
theorem single_beq {all : Ix.Set Ix.Name} (hsize : all.size = 1) {a b : Ix.Name} (ha : all.contains a = true)
    (hb : all.contains b = true) : (a == b) = true := by
  have hlen : all.toList.length = 1 := by rw [Std.HashSet.length_toList, hsize]
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨a', ha', ea⟩ := listed ha
  obtain ⟨b', hb', eb⟩ := listed hb
  rw [hx, List.mem_singleton] at ha' hb'
  subst ha' hb'
  exact BEq.trans ea (BEq.symm eb)

theorem length_filterMap_of_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    rw [List.filterMap_cons, hb, List.length_cons, List.length_cons,
      length_filterMap_of_isSome fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-! ## Definitions -/

theorem sourceData_name {ci : Ix.ConstantInfo} {d : Ix.Def} (h : EmissionDispatch.sourceData ci = some d) :
    d.name = ci.getCnst.name := by
  cases ci <;> simp only [EmissionDispatch.sourceData, reduceCtorEq, Option.some.injEq] at h <;> (subst h; rfl)

theorem sourceData_key {ci : Ix.ConstantInfo} {d : Ix.Def} (h : EmissionDispatch.sourceData ci = some d) :
    classKey (.defn d) = (ci.blockPosition, ci.getCnst.name) := by
  cases ci <;> simp only [EmissionDispatch.sourceData, reduceCtorEq, Option.some.injEq] at h <;> (subst h; rfl)

theorem fromDefinitionVal_eq (v : Ix.DefinitionVal) :
    MutConst.fromDefinitionVal v = .defn (definitionValData v) := by
  simp only [MutConst.fromDefinitionVal, definitionValData, MutConst.defn.injEq, Ix.Def.mk.injEq, true_and,
    and_true]
  generalize v.safety = s
  cases s <;> rfl

theorem sourceData_isSome {ci : Ix.ConstantInfo} (h : isDefinition ci = true) :
    (EmissionDispatch.sourceData ci).isSome = true := by
  cases ci <;> first | rfl | cases h

/-- **A definition-like constant's member is its definition.** -/
theorem memberOf_def {E : Ix.Name → Option Ix.ConstantInfo} {n : Ix.Name} {ci : Ix.ConstantInfo}
    (h : E n = some ci) (hd : isDefinition ci = true) :
    ∃ d, EmissionDispatch.sourceData ci = some d ∧ memberOf E n = some (.defn d) := by
  cases ci with
  | defnInfo v => exact ⟨_, rfl, by rw [memberOf, h]; exact congrArg some (fromDefinitionVal_eq v)⟩
  | thmInfo v => exact ⟨_, rfl, by rw [memberOf, h]; rfl⟩
  | opaqueInfo v => exact ⟨_, rfl, by rw [memberOf, h]; rfl⟩
  | _ => cases hd

/-- **A component group of definitions is sorted in Lean's order**, and its members are
definition-like. -/
theorem componentGroup_sorted {E : Ix.Environment} {members : Ix.Set Ix.Name} {ms : Array Ix.ConstantInfo}
    (h : componentGroup E members = some (.definitions ms)) :
    (ms.toList.Pairwise fun a b =>
      Ix.sourceOrderLt (b.blockPosition, b.getCnst.name) (a.blockPosition, a.getCnst.name) = false) ∧
      ∀ ci ∈ ms, isDefinition ci = true := by
  unfold componentGroup Ix.LeanIngress.componentGroupUsing at h
  generalize (Array.filterMapM (m := Id) (fun x => E.consts.get? x) members.toArray :
    Array Ix.ConstantInfo) = cis at h
  dsimp only [Id.run, bind, pure] at h
  generalize hothers : (cis.filter (fun x => !isFamily x)).qsort
    (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name)
      (b.blockPosition, b.getCnst.name)) = others at h
  have sorted : others.toList.Pairwise fun a b =>
      Ix.sourceOrderLt (b.blockPosition, b.getCnst.name) (a.blockPosition, a.getCnst.name) = false := by
    rw [← hothers]
    exact Ix.CompileCert.Canon.qsort_pairwise _ _ (fun _ => LeanOrder.lt_irrefl _)
      (fun _ _ _ => LeanOrder.lt_trans)
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i hall
        cases h
        exact ⟨sorted, fun ci hci => Array.all_eq_true'.mp hall ci hci⟩
      · exfalso
        obtain ⟨l⟩ := others
        rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
        · cases h
        · cases c <;> cases h
        · cases h

/-- **A definitions group of two or more runs as its definitions, in its own order**: its
compile block is a `FoldBlock` holding the group's names, and the block's records are those of
`compileMutualBlock` over the group's definitions (`defsOf`), one per class, run from the empty
state at the fold's snapshot. -/
theorem definitions_run {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) (two : 2 ≤ members.size) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      (∀ d ∈ TraceSegments.defsOf members, all.contains d.name = true) ∧
      ∃ out after, rawRun (compileMutualBlock (((TraceSegments.defsOf members).map MutConst.defn).map ([·])))
          (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
          (.ok out, after) ∧
        BlobWrites.Extends snap.cenv.blobs after c ∧ BlockRecords.recordsOf r = BlockRecords.recordsOf out := by
  have hcl : IsClosure env roots sub := P.source.1
  have hmemg : Group.definitions members ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨repS, allS, -, hcomp⟩ := GroupBlocks.component_of_groups sub (blocksOf sub) _ hmemg trivial
  obtain ⟨sortedM, defsM⟩ := componentGroup_sorted hcomp
  obtain ⟨-, storedM⟩ := LayoutExtra.componentGroup_kinded hcomp
  have namedE : ∀ k ci, env.consts.get? k = some ci → (ci.getCnst.name == k) = true :=
    fun k ci h => FamilyGroups.named_of_get P.compiled h
  have distinctM := DefinitionPremises.componentGroup_distinct
    (fun k ci h => namedE k ci (hcl.mem_env h)) hcomp
  -- every member is stored in the closure under its own name
  have own : ∀ ci ∈ members, (ci.getCnst.name, ci) ∈ sub.consts.toList := by
    intro ci hci
    obtain ⟨k, hk⟩ := storedM members rfl ci hci
    rw [inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)]
    exact hk
  -- the block of the first member
  have h0 : 0 < members.size := by omega
  obtain ⟨snap, rep, all, r, c, fb, -, hmem0⟩ := foldBlock_of P (own members[0] (Array.getElem_mem h0))
  have hin0 := hmem0 fun cv e => by
    have := defsM _ (Array.getElem_mem h0)
    rw [e] at this
    cases this
  obtain ⟨names, -, defE⟩ := GroupBlocks.group_names P scheduled hgr trivial fb.block
    (Array.mem_map.mpr ⟨members[0], Array.getElem_mem h0, rfl⟩) hin0
  have defE' := defE members rfl
  -- the members are the block's names
  have memIn : ∀ ci ∈ members, all.contains ci.getCnst.name = true := by
    intro ci hci
    obtain ⟨k, ci', hk, hci', e⟩ := (names ci.getCnst.name).mp (Array.mem_map.mpr ⟨ci, hci, rfl⟩)
    rw [e, Std.HashSet.contains_congr (namedE k ci' hci')]
    exact hk
  have sameC : ∀ ci ∈ members, ∀ {k ci'}, env.consts.get? k = some ci' → ci'.getCnst.name = ci.getCnst.name →
      ci' = ci := fun ci hci k ci' hk e =>
    FamilyGroups.same_stored P.compiled (SourceStoredNames.stored_input P (own ci hci)) hk e
  -- the definitions' members
  have defsIn : ∀ d ∈ TraceSegments.defsOf members, ∃ ci ∈ members, EmissionDispatch.sourceData ci = some d :=
    fun d hd => by
      obtain ⟨ci, hci, hd⟩ := List.mem_filterMap.mp hd
      exact ⟨ci, Array.mem_toList_iff.mp hci, hd⟩
  have memDefs : ∀ d ∈ TraceSegments.defsOf members, all.contains d.name = true := fun d hd => by
    obtain ⟨ci, hci, e⟩ := defsIn d hd
    rw [sourceData_name e]
    exact memIn ci hci
  obtain ⟨const, -, paths⟩ := runBlock_paths fb.ran
  rcases paths with ⟨hcond, -⟩ | ⟨-, cs, out, s₄, hloop, hout, hext, hrec⟩
  · -- a block of one name holds one member
    exfalso
    have hsize : all.size = 1 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1
    have h1 : 1 < members.size := by omega
    have e := single_beq hsize (memIn _ (Array.getElem_mem h0)) (memIn _ (Array.getElem_mem h1))
    have := List.pairwise_iff_getElem.mp distinctM 0 1 (by simp; omega) (by simp; omega) (by omega)
    simp only [List.getElem_map, Array.getElem_toList] at this
    rw [e] at this
    cases this
  refine ⟨snap, rep, all, r, c, fb, memDefs, out, s₄, ?_, hext, hrec⟩
  have hcs := membersLoop_eq _ _ hloop
  have hE : (fun x => ((snap.cenv, ({ all, current := blockKey rep all, mutCtx := default, univCtx := [] } :
      BlockEnv)).1.env.get? x)) = fun x => env.consts.get? x := funext fb.env
  rw [hE, Array.toList_empty, List.nil_append] at hcs
  have envCongr : ∀ a b, (a == b) = true → env.consts.get? a = env.consts.get? b := fun a b h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]
  -- the loop's members are the group's definitions
  have perm : cs.toList.Perm ((TraceSegments.defsOf members).map MutConst.defn) := by
    rw [hcs]
    refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
    · exact filterMap_nodup Std.HashSet.distinct_toList fun a b x ha hb =>
        BEq.trans (BEq.symm (memberOf_name namedE ha)) (memberOf_name namedE hb)
    · show List.Pairwise _ _
      rw [List.pairwise_map]
      refine (List.pairwise_map.mp distinctM).filterMap _ fun a a' h d hd d' hd' e => ?_
      cases e
      rw [← sourceData_name hd, ← sourceData_name hd', BEq.rfl] at h
      cases h
    · obtain ⟨n, hn, hnm⟩ := List.mem_filterMap.mp hm
      have hnall := contains_of_listed hn
      obtain ⟨ci, hci⟩ : ∃ ci, env.consts.get? n = some ci := by
        unfold memberOf at hnm
        split at hnm <;> first | exact ⟨_, ‹_›⟩ | cases hnm
      obtain ⟨d, hd, hdm⟩ := memberOf_def hci (defE' n ci hnall hci)
      rw [hdm] at hnm
      cases hnm
      obtain ⟨ci', hci', e⟩ := Array.mem_map.mp ((names ci.getCnst.name).mpr ⟨n, ci, hnall, hci, rfl⟩)
      have hcc : ci = ci' := sameC ci' hci' hci e.symm
      subst hcc
      exact List.mem_map.mpr ⟨d, List.mem_filterMap.mpr ⟨ci, Array.mem_toList_iff.mpr hci', hd⟩, rfl⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
      obtain ⟨ci, hci, hdci⟩ := defsIn d hd
      obtain ⟨k, ci', hk, hci', e⟩ := (names ci.getCnst.name).mp (Array.mem_map.mpr ⟨ci, hci, rfl⟩)
      have hcc : ci' = ci := sameC ci hci hci' e.symm
      subst hcc
      obtain ⟨k', hk', ekk⟩ := listed hk
      obtain ⟨d', hd', hdm⟩ := memberOf_def hci' (defsM _ hci)
      rw [hdci] at hd'
      cases hd'
      refine List.mem_filterMap.mpr ⟨k', hk', ?_⟩
      rw [← memberOf_congr envCongr ekk, hdm]
  -- quotient Source's order is Lean's
  have sortedX : ((TraceSegments.defsOf members).map MutConst.defn).Pairwise
      fun a b => Ix.sourceOrderLt (classKey b) (classKey a) = false := by
    rw [List.pairwise_map]
    refine sortedM.filterMap _ fun a a' h d hd d' hd' => ?_
    rw [sourceData_key hd, sourceData_key hd']
    exact h
  have inX : ∀ d, MutConst.defn d ∈ (TraceSegments.defsOf members).map MutConst.defn →
      ∃ ci ∈ members, EmissionDispatch.sourceData ci = some d := fun d hd => by
    obtain ⟨d', hd', e⟩ := List.mem_map.mp hd
    injection e with e
    subst e
    exact defsIn _ hd'
  -- the compile's own list of definitions, for `apart`
  have hsc := LeanOrder.sourceClasses_def cs
  generalize hL : (cs.zipIdx.qsort (LeanOrder.zipBefore classKey)).toList.map (·.1) = L at hsc
  have permL : L.Perm cs.toList := by
    rw [← hL]
    have p := ((Ix.CompileCert.Canon.qsort_perm cs.zipIdx (LeanOrder.zipBefore classKey)).toList).map (·.1)
    rw [Array.toList_zipIdx, List.zipIdx_map_fst] at p
    exact p
  have defnL : ∀ m ∈ L, GroupBlocks.IsDefn m := fun m hm => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp ((permL.trans perm).mem_iff.mp hm)
    trivial
  generalize hD : L.filterMap GroupBlocks.toDef = D
  have hDL : D.map MutConst.defn = L := by
    rw [← hD]
    exact GroupBlocks.defs_map L defnL
  rw [← hDL] at hsc permL
  rw [hsc] at hout
  have permD := permL.trans perm
  have hlen : D.length = members.size := by
    have := permD.length_eq
    rw [List.length_map, List.length_map, TraceSegments.defsOf, length_filterMap_of_isSome, Array.length_toList]
      at this
    · exact this
    · intro ci hci
      exact sourceData_isSome (defsM ci (Array.mem_toList_iff.mp hci))
  have apartD := BlockPublication.apart fb.ran fb.published (by omega : 2 ≤ D.length) hout hrec
    fun j hj => by
      obtain ⟨ci, hci, e⟩ := inX D[j] (permD.mem_iff.mp (List.mem_map_of_mem (List.getElem_mem hj)))
      rw [sourceData_name e, SourceStoredNames.stored_get (own ci hci)]
      rfl
  -- no two members tie: they would have one key and so one address
  have noTie : ∀ a ∈ (TraceSegments.defsOf members).map MutConst.defn,
      ∀ b ∈ (TraceSegments.defsOf members).map MutConst.defn,
      Ix.sourceOrderLt (classKey a) (classKey b) = false → Ix.sourceOrderLt (classKey b) (classKey a) = false →
        a = b := by
    intro a ha b hb h₁ h₂
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (permD.mem_iff.mpr ha)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (permD.mem_iff.mpr hb)
    have tie := (LeanOrder.tie_of_not_lt h₁ h₂).2
    have hi' : i < D.length := by simpa using hi
    have hj' : j < D.length := by simpa using hj
    simp only [List.getElem_map] at tie ⊢
    obtain ⟨ci, hci, ei⟩ := inX D[i] (permD.mem_iff.mp (List.mem_map_of_mem (List.getElem_mem hi')))
    obtain ⟨cj, hcj, ej⟩ := inX D[j] (permD.mem_iff.mp (List.mem_map_of_mem (List.getElem_mem hj')))
    have si : (D[i].name, ci) ∈ sub.consts.toList := by
      rw [sourceData_name ei]
      exact own ci hci
    have sj : (D[j].name, cj) ∈ sub.consts.toList := by
      rw [sourceData_name ej]
      exact own cj hcj
    have hij := apartD i hi' j hj' (addr_of_key P si sj (key_of_tie tie))
    subst hij
    rfl
  have hsc' := LeanOrder.sourceClasses_eq perm sortedX noTie
  rw [← hsc, hsc'] at hout
  exact hout

/-! ## An inductive group's types -/

/-- Distinct keys give distinct member names. -/
theorem names_nodup : ∀ {ms : List MutConst}, Canon.KeysDistinct ms → (ms.map MutConst.name).Nodup
  | [], _ => List.nodup_nil
  | m :: ms, h => by
    unfold Canon.KeysDistinct at h
    rw [List.flatMap_cons, List.nodup_append] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, names_nodup h.2.1⟩
    obtain ⟨m', hm', e⟩ := List.mem_map.mp hm
    exact h.2.2 m.name (by simp [Canon.keysOf]) m.name
      (List.mem_flatMap.mpr ⟨m', hm', by simp [Canon.keysOf, e]⟩) rfl

/-- A closure constant looked up is stored under its own name. -/
theorem own_of_get {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) {x : Ix.Name} {ci : Ix.ConstantInfo}
    (h : sub.consts.get? x = some ci) : (ci.getCnst.name, ci) ∈ sub.consts.toList := by
  obtain ⟨k, hk⟩ := SourceStoredNames.lookup_stored h
  rw [inputsNamed P.compiled k ci (SourceStoredNames.stored_input P hk)]
  exact hk

theorem mapM_ctorOf {E : Ix.Name → Option Ix.ConstantInfo} :
    ∀ {xs : List Ix.Name} {cs : List Ix.ConstructorVal}, List.Forall₂ (fun x cv => E x = some (.ctorInfo cv)) xs cs →
      xs.mapM (ctorOf E) = some cs
  | [], [], .nil => rfl
  | x :: xs, cv :: cs, .cons h rest => by
    simp [List.mapM_cons, ctorOf, h, mapM_ctorOf rest]

/-- The facts of an inductive group's shape the run needs: its first type's block, its types and
constructors as input constants under their own names, and each type's constructors those its
list names. -/
theorem inductive_facts {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs)) :
    ∃ (n : Ix.Name) (v : Ix.InductiveVal), (n, .inductInfo v) ∈ sub.consts.toList ∧ v.all[0]? = some n ∧
      blockRecursors v ((FamilyGroups.recsTable sub).getD n #[]) = .ok recs ∧
      ctors.size = types.size ∧ types.size = v.all.size ∧
      (∀ j (hj : j < types.size), types[j].all = v.all ∧
        ∃ hj' : j < v.all.size, sub.consts.get? v.all[j] = some (.inductInfo types[j])) ∧
      (∀ j (hj : j < types.size), env.consts.get? types[j].cnst.name = some (.inductInfo types[j]) ∧
        (types[j].cnst.name, .inductInfo types[j]) ∈ sub.consts.toList) ∧
      (∀ j (hj : j < ctors.size) k (hk : k < ctors[j].size),
        env.consts.get? ctors[j][k].cnst.name = some (.ctorInfo ctors[j][k])) ∧
      ∀ j (hj : j < types.size) (hj' : j < ctors.size),
        types[j].ctors.toList.mapM (ctorOf (env.consts.get? ·)) = some ctors[j].toList := by
  have hcl : IsClosure env roots sub := P.source.1
  have hmem : Group.inductive types ctors recs ∈ groupsOf sub (blocksOf sub) := Array.mem_of_getElem? hgr
  obtain ⟨n, v, hnv, head, hg⟩ := FamilyGroups.inductive_origin hmem
  rcases FamilyGroups.inductiveGroup_shape hg with ⟨_, _, e⟩ | ⟨_, _, _, e, htypes, hctors, hrecs⟩
  · cases e
  obtain ⟨e₁, e₂, e₃⟩ := Group.inductive.inj e
  subst e₁ e₂ e₃
  have hlenT := InductiveCompile.forall₂_length htypes
  have hlenC := InductiveCompile.forall₂_length hctors
  simp only [Array.length_toList] at hlenT hlenC
  have typeAt : ∀ j (hj : j < types.size), ∃ hj' : j < v.all.size,
      sub.consts.get? v.all[j] = some (.inductInfo types[j]) ∧
        types[j].all.isEqv v.all Ix.Name.beqRaw = true := fun j hj => by
    have hj' : j < v.all.size := by omega
    have := InductiveCompile.forall₂_getElem htypes j (by simpa using hj') (by simpa using hj)
    simp only [Array.getElem_toList] at this
    exact ⟨hj', this⟩
  have typeGet : ∀ j (hj : j < types.size), env.consts.get? types[j].cnst.name = some (.inductInfo types[j]) ∧
      (types[j].cnst.name, .inductInfo types[j]) ∈ sub.consts.toList := fun j hj => by
    obtain ⟨_, hget, -⟩ := typeAt j hj
    exact ⟨FamilyGroups.get_own P.compiled (hcl.mem_env hget), own_of_get P hget⟩
  have ctorAt : ∀ j (hj : j < types.size) (hj' : j < ctors.size),
      List.Forall₂ (fun x cv => sub.consts.get? x = some (.ctorInfo cv)) types[j].ctors.toList ctors[j].toList := by
    intro j hj hj'
    have hall := InductiveCompile.forall₂_getElem hctors j (by simpa using hj) (by simpa using hj')
    simp only [Array.getElem_toList] at hall
    have hlen := InductiveCompile.forall₂_length hall
    simp only [Array.toList_zipIdx, List.length_zipIdx, Array.length_toList] at hlen
    refine InductiveCompile.forall₂_of_getElem (by simpa using hlen) fun k h₁ h₂ => ?_
    have := InductiveCompile.forall₂_getElem hall k (by simpa using h₁) h₂
    simp only [Array.toList_zipIdx, List.getElem_zipIdx, Array.getElem_toList] at this
    simpa using this.1
  refine ⟨n, v, hnv, head, hrecs, by omega, by omega, fun j hj => ?_, typeGet, fun j hj k hk => ?_, fun j hj hj' => ?_⟩
  · obtain ⟨hj', hget, heqv⟩ := typeAt j hj
    exact ⟨FamilyGroups.eq_of_isEqv_raw heqv, hj', hget⟩
  · have hj₂ : j < types.size := by omega
    have hl := InductiveCompile.forall₂_length (ctorAt j hj₂ hj)
    simp only [Array.length_toList] at hl
    have := InductiveCompile.forall₂_getElem (ctorAt j hj₂ hj) k (by simp; omega) (by simpa using hk)
    simp only [Array.getElem_toList] at this
    exact FamilyGroups.get_own P.compiled (hcl.mem_env this)
  · have h := ctorAt j hj hj'
    exact mapM_ctorOf (InductiveCompile.forall₂_of_getElem (InductiveCompile.forall₂_length h)
      fun k h₁ h₂ => hcl.mem_env (InductiveCompile.forall₂_getElem h k h₁ h₂))

/-- **An inductive group's types sit at their positions in their block**, when the group's
members have distinct names. -/
theorem types_positions {v : Ix.InductiveVal} {types : Array Ix.InductiveVal} {sub : Ix.Environment}
    (hsize : types.size = v.all.size)
    (typeAt : ∀ j (hj : j < types.size), types[j].all = v.all ∧
      ∃ hj' : j < v.all.size, sub.consts.get? v.all[j] = some (.inductInfo types[j]))
    (named : ∀ {x : Ix.Name} {ci : Ix.ConstantInfo}, sub.consts.get? x = some ci → (ci.getCnst.name == x) = true)
    (congr : ∀ a b, (a == b) = true → sub.consts.get? a = sub.consts.get? b)
    (distinct : ∀ j (hj : j < types.size) k (hk : k < types.size), types[j].cnst.name = types[k].cnst.name → j = k) :
    ∀ j (hj : j < types.size), Ix.blockPosition types[j].all types[j].cnst.name = j := by
  intro j hj
  obtain ⟨hall, hj', hget⟩ := typeAt j hj
  unfold Ix.blockPosition
  rw [hall]
  have hfind : v.all.findIdx? (· == types[j].cnst.name) = some j := by
    rw [Array.findIdx?_eq_some_iff_getElem]
    refine ⟨hj', BEq.symm (named hget), fun k hkj e => ?_⟩
    have hk : k < types.size := by omega
    obtain ⟨-, hk', hgetk⟩ := typeAt k hk
    have e' : (v.all[k] == v.all[j]) = true := BEq.trans e (named hget)
    rw [congr _ _ e', hget] at hgetk
    have := distinct k hk j hj (by
      have := Ix.ConstantInfo.inductInfo.inj (Option.some.inj hgetk)
      rw [this])
    omega
  rw [hfind]
  rfl

/-- **An inductive group's types have distinct names** when its members' keys are distinct. -/
theorem types_distinct {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    (hcsize : ctors.size = types.size) (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc)) :
    ∀ j (hj : j < types.size) k (hk : k < types.size), types[j].cnst.name = types[k].cnst.name → j = k := by
  have hlenI := InductiveCompile.indsOf_length hcsize
  have nodupN := names_nodup distinct
  intro j hj k hk e
  rcases Nat.lt_trichotomy j k with h | h | h
  · have := List.pairwise_iff_getElem.mp nodupN j k (by simp; omega) (by simp; omega) h
    simp only [List.getElem_map, InductiveCompile.indsOf_getElem hcsize] at this
    exact absurd e this
  · exact h
  · have := List.pairwise_iff_getElem.mp nodupN k j (by simp; omega) (by simp; omega) h
    simp only [List.getElem_map, InductiveCompile.indsOf_getElem hcsize] at this
    exact absurd e.symm this

/-- **An inductive group's types run as the group's members, in its order**: the compile block
of its types is a `FoldBlock` holding exactly the group's types and constructors, and its records
are those of `compileMutualBlock` over `indsOf types ctors`, one per class. -/
theorem types_run {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fbk : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc)) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      (∀ x, all.contains x = true ↔
        (∃ (i : Nat) (_ : i < types.size), (types[i].cnst.name == x) = true) ∨
        ∃ (i : Nat) (hi : i < ctors.size) (k : Nat) (_ : k < ctors[i].size), (ctors[i][k].cnst.name == x) = true) ∧
      ∃ out after, rawRun (compileMutualBlock (((indsOf types ctors).map MutConst.indc).map ([·])))
          (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
          (.ok out, after) ∧
        BlobWrites.Extends snap.cenv.blobs after c ∧ BlockRecords.recordsOf r = BlockRecords.recordsOf out := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨n, v, -, head, -, hcsize, hsizeT, typeAt, typeGet, ctorGet, ctorsOf⟩ := inductive_facts P hgr
  have namedE : ∀ k ci, env.consts.get? k = some ci → (ci.getCnst.name == k) = true :=
    fun k ci h => FamilyGroups.named_of_get P.compiled h
  have envCongr : ∀ a b, (a == b) = true → env.consts.get? a = env.consts.get? b := fun a b h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]
  have subCongr : ∀ a b, (a == b) = true → sub.consts.get? a = sub.consts.get? b := fun a b h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]
  have hlenI := InductiveCompile.indsOf_length hcsize
  have hxs : ∀ j (hj : j < ((indsOf types ctors).map MutConst.indc).length),
      ((indsOf types ctors).map MutConst.indc)[j] =
        .indc (indOf (types[j]'(by simp at hj; omega)) (ctors[j]'(by simp at hj; omega))) := by
    intro j hj
    simp only [List.getElem_map]
    rw [InductiveCompile.indsOf_getElem hcsize]
  have distinctT := types_distinct hcsize distinct
  have positions := types_positions hsizeT typeAt
    (fun h => FamilyGroups.named_of_get P.compiled (hcl.mem_env h)) subCongr distinctT
  -- the block of the first type
  have h0 : 0 < types.size := by
    have : 0 < v.all.size := (Array.getElem?_eq_some_iff.mp head).1
    omega
  obtain ⟨snap, rep, all, r, c, fb, -, hmem0⟩ := foldBlock_of P (typeGet 0 h0).2
  have hin0 := hmem0 fun cv e => by cases e
  have memAll := FamilyGroups.inductive_block_at P fbk hgr fb.block h0 hin0
  -- a name of the block is a type or a constructor, so the block is an inductive block
  obtain ⟨const, hconst, paths⟩ := runBlock_paths fb.ran
  rcases paths with ⟨hcond, -⟩ | ⟨-, cs, out, s₄, hloop, hout, hext, hrec⟩
  · exfalso
    rw [fb.env] at hconst
    have hkey := (memAll _).mp (blockKey_mem (lo := rep) (Condense.condense_nonempty fb.block))
    rcases hkey with ⟨j, hj, e⟩ | ⟨j, hj, k, hk, e⟩
    · rw [← envCongr _ _ e, (typeGet j hj).1] at hconst
      cases hconst
      simp [isIndConst] at hcond
    · rw [← envCongr _ _ e, ctorGet j hj k hk] at hconst
      cases hconst
      simp [isIndConst] at hcond
  refine ⟨snap, rep, all, r, c, fb, memAll, out, s₄, ?_, hext, hrec⟩
  have hcs := membersLoop_eq _ _ hloop
  have hE : (fun x => ((snap.cenv, ({ all, current := blockKey rep all, mutCtx := default, univCtx := [] } :
      BlockEnv)).1.env.get? x)) = fun x => env.consts.get? x := funext fb.env
  rw [hE, Array.toList_empty, List.nil_append] at hcs
  -- a type's member is the group's
  have typeMember : ∀ j (hj : j < types.size),
      memberOf (fun x => env.consts.get? x) types[j].cnst.name =
        some (.indc (indOf types[j] (ctors[j]'(by omega)))) := by
    intro j hj
    simp only [memberOf, (typeGet j hj).1, ctorsOf j hj (by omega), Option.map_some, Array.toArray_toList]
  have ⟨nodupX, sortedX, noTieX⟩ := positioned (xs := (indsOf types ctors).map MutConst.indc) fun j hj => by
    rw [hxs j hj]
    exact positions j (by simp at hj; omega)
  have perm : cs.toList.Perm ((indsOf types ctors).map MutConst.indc) := by
    rw [hcs]
    refine (List.perm_ext_iff_of_nodup ?_ nodupX).mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
    · exact filterMap_nodup Std.HashSet.distinct_toList fun a b x ha hb =>
        BEq.trans (BEq.symm (memberOf_name namedE ha)) (memberOf_name namedE hb)
    · obtain ⟨x, hx, hxm⟩ := List.mem_filterMap.mp hm
      rcases (memAll x).mp (contains_of_listed hx) with ⟨j, hj, e⟩ | ⟨j, hj, k, hk, e⟩
      · rw [← memberOf_congr envCongr e, typeMember j hj] at hxm
        cases hxm
        have hj' : j < ((indsOf types ctors).map MutConst.indc).length := by simp; omega
        rw [← hxs j hj']
        exact List.getElem_mem hj'
      · rw [← memberOf_congr envCongr e, memberOf, ctorGet j hj k hk] at hxm
        cases hxm
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
      have hjT : j < types.size := by simp at hj; omega
      obtain ⟨x, hx, e⟩ := listed ((memAll _).mpr (.inl ⟨j, hjT, BEq.rfl⟩))
      refine List.mem_filterMap.mpr ⟨x, hx, ?_⟩
      rw [← memberOf_congr envCongr e, typeMember j hjT, hxs j hj]
  rw [LeanOrder.sourceClasses_eq perm sortedX noTieX] at hout
  exact hout

/-! ## An inductive group's recursors -/

/-- **The digits of `j + 1`, read back** as `recursorFamilyPosition` reads them. -/
theorem digits_round_trip (j : Nat) :
    (toString (j + 1)).isEmpty = false ∧ (toString (j + 1)).all Char.isDigit = true ∧
      (toString (j + 1)).foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0 = j + 1 := by
  refine ⟨String.isEmpty_eq_false_iff.mpr (by rw [Nat.toString_eq_repr]; exact Nat.repr_ne_empty), ?_, ?_⟩
  · rw [String.all_bool_eq, Nat.toString_eq_repr, Nat.toList_repr, List.all_eq_true]
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  · rw [String.foldl_eq_foldl_toList, Nat.toString_eq_repr, Nat.toList_repr]
    have h := Nat.ofDigitChars_ten_toDigits (n := j + 1)
    rw [Nat.ofDigitChars_eq_foldl] at h
    have hf : (fun (n : Nat) (c : Char) => n * 10 + (c.toNat - '0'.toNat)) =
        fun sofar c => 10 * sofar + (c.toNat - '0'.toNat) := by
      funext n c
      rw [Nat.mul_comm]
    rw [hf]
    exact h

theorem dropPrefix_rec (d : String) :
    ∃ sl : String.Slice, ("rec_" ++ d).dropPrefix? "rec_" = some sl ∧ sl.copy = d := by
  cases h : ("rec_" ++ d).dropPrefix? "rec_" with
  | none =>
    exfalso
    rw [String.dropPrefix?_eq_dropPrefix?_toSlice, String.Slice.dropPrefix?_eq_none_iff, String.startsWith_toSlice,
      String.startsWith_string_eq_false_iff] at h
    exact h (by rw [String.toList_append]; exact List.prefix_append _ _)
  | some sl =>
    refine ⟨sl, rfl, ?_⟩
    have e := String.eq_append_of_dropPrefix?_string_eq_some h
    exact ((String.append_right_inj "rec_").mp e).symm

theorem rec_ne (x : String) : "rec_" ++ x ≠ "rec" := by
  intro h
  have := congrArg String.length h
  rw [String.length_append, (by decide : "rec_".length = 4), (by decide : "rec".length = 3)] at this
  omega

/-- A name `isStrName` accepts is `parent.s`. -/
theorem isStrName_eq {parent : Ix.Name} {s : String} {n : Ix.Name}
    (h : Ix.LeanIngress.isStrName parent s n = true) : ∃ hash, n = .str parent s hash := by
  cases n with
  | str p s' hash =>
    simp only [Ix.LeanIngress.isStrName, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Ix.Name.beqRaw_iff.mp h.2]
    exact ⟨hash, rfl⟩
  | _ => cases h

/-- **`X.rec` sits at `X`'s position** in a family whose `all` lists its members once. -/
theorem position_own {r : Ix.RecursorVal} {all : Array Ix.Name} {j : Nat} (hj : j < all.size)
    (hall : r.all = all) (hname : Ix.LeanIngress.isStrName all[j] "rec" r.cnst.name = true)
    (distinct : ∀ k (hk : k < all.size), (all[k] == all[j]) = true → k = j) (bound : all.size < 2 ^ 63) :
    (recursorFamilyPosition r).toNat = j := by
  obtain ⟨hash, hn⟩ := isStrName_eq hname
  have hpos : recursorFamilyPosition r = match r.all.findIdx? (· == all[j]) with
      | some i => UInt64.ofNat i
      | none => recursorFamilyNoPosition := by
    unfold recursorFamilyPosition
    rw [hn]
    rfl
  have hf : all.findIdx? (· == all[j]) = some j := Array.findIdx?_eq_some_iff_getElem.mpr
    ⟨hj, BEq.rfl, fun k hk e => absurd (distinct k (by omega) e) (by omega)⟩
  rw [hpos, hall, hf]
  show (UInt64.ofNat j).toNat = j
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- **`first.rec_(j+1)` sits after the block**, at `all.size + j`. -/
theorem position_aux {r : Ix.RecursorVal} {all : Array Ix.Name} {first : Ix.Name} {j : Nat}
    (hall : r.all = all) (head : all[0]? = some first)
    (hname : Ix.LeanIngress.isStrName first s!"rec_{j + 1}" r.cnst.name = true) (bound : all.size + j < 2 ^ 63) :
    (recursorFamilyPosition r).toNat = all.size + j := by
  obtain ⟨hash, hn⟩ := isStrName_eq hname
  have hs : s!"rec_{j + 1}" = "rec_" ++ toString (j + 1) := rfl
  rw [hs] at hn
  obtain ⟨sl, hsl, hcopy⟩ := dropPrefix_rec (toString (j + 1))
  obtain ⟨hne, hdig, hfold⟩ := digits_round_trip j
  have hnone : recursorFamilyNoPosition.toNat = 18446744073709551615 := rfl
  unfold recursorFamilyPosition
  rw [hn]
  split
  · rename_i heq
    simp only [Ix.Name.str.injEq] at heq
    exact absurd heq.2.1 (rec_ne _)
  · rename_i heq
    simp only [Ix.Name.str.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rw [hsl]
    dsimp only
    have ht : sl.toString = toString (j + 1) := hcopy
    have hc : (decide (1 ≤ j + 1) && r.all[0]? == some first &&
        decide (r.all.size + (j + 1) - 1 < recursorFamilyNoPosition.toNat)) = true := by
      rw [hall, head, hnone]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by omega, (BEq.rfl : (first == first) = true)⟩, by omega⟩
    rw [ht, hne, hdig, hfold]
    simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hc]
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by rw [hall]; omega), hall]
    omega
  · rename_i hn'
    exact absurd rfl (hn' _ _ _)

/-- **`blockRecursors`' names**: `X.rec` for each `X` of the block, then `first.rec_(j+1)`. -/
theorem blockRecursors_names {first : Ix.InductiveVal} {cands recs : Array Ix.RecursorVal}
    (h : blockRecursors first cands = .ok recs) :
    recs.size = first.all.size + first.numNested ∧
      (∀ j (hj : j < first.all.size), ∃ hr : j < recs.size,
        Ix.LeanIngress.isStrName first.all[j] "rec" recs[j].cnst.name = true) ∧
      ∀ j (_ : j < first.numNested), ∃ hr : first.all.size + j < recs.size,
        Ix.LeanIngress.isStrName first.cnst.name s!"rec_{j + 1}" recs[first.all.size + j].cnst.name = true := by
  unfold blockRecursors at h
  obtain ⟨own, hown, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  obtain ⟨aux, haux, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have fo := ReaderUnits.array_mapM_ok hown
  have fa := ReaderUnits.array_mapM_ok haux
  have lo := InductiveCompile.forall₂_length fo
  have la := InductiveCompile.forall₂_length fa
  simp only [Array.length_toList, Array.toList_range, List.length_range] at lo la
  refine ⟨by rw [Array.size_append]; omega, fun j hj => ⟨by rw [Array.size_append]; omega, ?_⟩,
    fun j hj => ⟨by rw [Array.size_append]; omega, ?_⟩⟩
  · have hx := InductiveCompile.forall₂_getElem fo j (by simpa using hj) (by simp; omega)
    simp only [Array.getElem_toList] at hx
    rw [Array.getElem_append_left (by omega)]
    split at hx
    · rename_i r' hr'
      cases hx
      have := Array.find?_some hr'
      exact this
    · cases hx
  · have hx := InductiveCompile.forall₂_getElem fa j (by simpa using hj) (by simp; omega)
    simp only [Array.getElem_toList, Array.toList_range, List.getElem_range] at hx
    rw [Array.getElem_append_right (by omega)]
    simp only [show first.all.size + j - own.size = j by omega]
    split at hx
    · rename_i r' hr'
      cases hx
      have := Array.find?_some hr'
      exact this
    · cases hx

/-- **An inductive group's recursors run as a family in `blockRecursors`' order, or alone under
their own name when there is one**: the compile block of its recursors is a `FoldBlock` holding
exactly the group's recursors, and its records are those of `compileMutualBlock` over the
recursors, one per class, or, for a lone recursor, of its single-constant compile, the block's
key being its name. -/
theorem recursors_run {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fbk : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc)) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      (∀ x, all.contains x = true ↔ ∃ (j : Nat) (_ : j < recs.size), (recs[j].cnst.name == x) = true) ∧
      ∃ out after,
        (rawRun (compileMutualBlock ((recs.toList.map MutConst.recr).map ([·])))
            (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
            (.ok out, after) ∨
          ∃ r', recs.toList = [r'] ∧ blockKey rep all = r'.cnst.name ∧
            rawRun (compileConstantInfo (.recInfo r'))
              (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
              (.ok out, after)) ∧
        BlobWrites.Extends snap.cenv.blobs after c ∧ BlockRecords.recordsOf r = BlockRecords.recordsOf out := by
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨n, v, hnv, head, hrecs, hcsize, hsizeT, typeAt, -, -, -⟩ := inductive_facts P hgr
  have namedE : ∀ k ci, env.consts.get? k = some ci → (ci.getCnst.name == k) = true :=
    fun k ci h => FamilyGroups.named_of_get P.compiled h
  have envCongr : ∀ a b, (a == b) = true → env.consts.get? a = env.consts.get? b := fun a b h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]
  have subCongr : ∀ a b, (a == b) = true → sub.consts.get? a = sub.consts.get? b := fun a b h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]
  have hnE : env.consts.get? n = some (.inductInfo v) := hcl.mem_env (SourceStoredNames.stored_get hnv)
  have hvn : v.cnst.name = n := inputsNamed P.compiled n _ (SourceStoredNames.stored_input P hnv)
  -- the block lists its types once
  have distinctT := types_distinct hcsize distinct
  have allDistinct : ∀ k (hk : k < v.all.size) j (hj : j < v.all.size), (v.all[k] == v.all[j]) = true → k = j := by
    intro k hk j hj e
    obtain ⟨-, _, hk'⟩ := typeAt k (by omega)
    obtain ⟨-, _, hj'⟩ := typeAt j (by omega)
    rw [subCongr _ _ e, hj'] at hk'
    refine distinctT k (by omega) j (by omega) ?_
    rw [Ix.ConstantInfo.inductInfo.inj (Option.some.inj hk')]
  -- the recursors, stored under their own names, in the block of `n`
  obtain ⟨hsizeR, ownN, auxN⟩ := blockRecursors_names hrecs
  have cand : ∀ r ∈ recs, ∃ k, (k, Ix.ConstantInfo.recInfo r) ∈ sub.consts.toList ∧ r.all[0]? = some n :=
    fun r hr => FamilyGroups.recsTable_mem (SourceStoredNames.blockRecursors_mem hrecs r hr)
  have recOwn : ∀ j (hj : j < recs.size), (recs[j].cnst.name, .recInfo recs[j]) ∈ sub.consts.toList ∧
      env.consts.get? recs[j].cnst.name = some (.recInfo recs[j]) ∧ recs[j].all[0]? = some n := by
    intro j hj
    obtain ⟨k, hk, h0⟩ := cand _ (Array.getElem_mem hj)
    have e : recs[j].cnst.name = k := inputsNamed P.compiled k _ (SourceStoredNames.stored_input P hk)
    rw [e]
    exact ⟨hk, SourceStoredNames.stored_get (SourceStoredNames.stored_input P hk), h0⟩
  have hv0 : 0 < v.all.size := (Array.getElem?_eq_some_iff.mp head).1
  have hR : 0 < recs.size := by omega
  obtain ⟨snap, rep, all, r, c, fb, ⟨a₀, b₀, hclaim⟩, hmem0⟩ := foldBlock_of P (recOwn 0 hR).1
  have hin0 := hmem0 fun cv e => by cases e
  have memAll := FamilyGroups.recursor_block_at P fbk hgr fb.block hR hin0
  -- every recursor carries the family's `all`, and the family fits 64-bit positions
  have recAll : ∀ j (hj : j < recs.size), recs[j].all = v.all ∧ v.all.size + v.numNested < 2 ^ 63 := by
    intro j hj
    obtain ⟨-, hget, h0⟩ := recOwn j hj
    obtain ⟨first, iv, hfirst, hiv, hall, hbound, -⟩ :=
      (fbk rep all fb.block _ ((memAll _).mpr ⟨j, hj, BEq.rfl⟩)).2.2 _ hget
    have hfn : first = n := Option.some.inj (hfirst.symm.trans h0)
    subst hfn
    rw [hnE] at hiv
    cases hiv
    exact ⟨hall, hbound⟩
  have bound := (recAll 0 hR).2
  -- each recursor sits at its position in the family
  have positions : ∀ j (hj : j < recs.size), (recursorFamilyPosition recs[j]).toNat = j := by
    intro j hj
    by_cases hjA : j < v.all.size
    · obtain ⟨_, hname⟩ := ownN j hjA
      exact position_own hjA (recAll j hj).1 hname (fun k hk e => allDistinct k hk j hjA e) (by omega)
    · obtain ⟨j', rfl⟩ : ∃ j', j = v.all.size + j' := ⟨j - v.all.size, by omega⟩
      obtain ⟨_, hname⟩ := auxN j' (by omega)
      rw [hvn] at hname
      exact position_aux (recAll _ hj).1 head hname (by omega)
  have hxs : ∀ j (hj : j < (recs.toList.map MutConst.recr).length),
      (recs.toList.map MutConst.recr)[j] = .recr (recs[j]'(by simpa using hj)) := by
    intro j hj
    simp
  have ⟨nodupX, sortedX, noTieX⟩ := positioned (xs := recs.toList.map MutConst.recr) fun j hj => by
    rw [hxs j hj]
    exact positions j _
  -- the block's key is one of the recursors
  obtain ⟨const, hconst, paths⟩ := runBlock_paths fb.ran
  rw [fb.env] at hconst
  obtain ⟨jk, hjk, ek⟩ := (memAll _).mp (blockKey_mem (lo := rep) (Condense.condense_nonempty fb.block))
  rw [← envCongr _ _ ek, (recOwn jk hjk).2.1] at hconst
  cases hconst
  rcases paths with ⟨hcond, hs⟩ | ⟨-, cs, out, s₄, hloop, hout, hext, hrec⟩
  · -- a lone recursor, compiled alone under its own name
    have hsize : all.size = 1 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1
    have h1 : recs.size = 1 := by
      refine Nat.le_antisymm (Nat.not_lt.mp fun h1 => ?_) hR
      have e := single_beq hsize ((memAll _).mpr ⟨0, hR, BEq.rfl⟩) ((memAll _).mpr ⟨1, h1, BEq.rfl⟩)
      have g := (recOwn 0 hR).2.1
      rw [envCongr _ _ e, (recOwn 1 h1).2.1] at g
      have e01 : recs[1] = recs[0] := Ix.ConstantInfo.recInfo.inj (Option.some.inj g)
      have p1 := positions 1 h1
      rw [e01, positions 0 hR] at p1
      cases p1
    have hjk0 : jk = 0 := by omega
    subst hjk0
    have hproj := InductiveSegments.lone_projections hs
    have hkey : recs[0].cnst.name = blockKey rep all := by
      rcases ClosureClaims.claim_name hclaim with e | ⟨row, hrow, -⟩
      · exact e
      · rw [hproj] at hrow
        simp at hrow
    have hl : recs.toList = [recs[0]] := by
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (by rw [Array.length_toList]; exact h1)
      have h := Array.getElem_toList (xs := recs) (i := 0) (h := by rw [Array.length_toList]; omega)
      simp only [ha, List.getElem_cons_zero] at h
      rw [ha, h]
    exact ⟨snap, rep, all, r, c, fb, memAll, r, c, .inr ⟨recs[0], hl, hkey.symm, hs⟩, .refl _ _, rfl⟩
  · refine ⟨snap, rep, all, r, c, fb, memAll, out, s₄, .inl ?_, hext, hrec⟩
    have hcs := membersLoop_eq _ _ hloop
    have hE : (fun x => ((snap.cenv, ({ all, current := blockKey rep all, mutCtx := default, univCtx := [] } :
        BlockEnv)).1.env.get? x)) = fun x => env.consts.get? x := funext fb.env
    rw [hE, Array.toList_empty, List.nil_append] at hcs
    have recMember : ∀ j (hj : j < recs.size),
        memberOf (fun x => env.consts.get? x) recs[j].cnst.name = some (.recr recs[j]) := by
      intro j hj
      simp only [memberOf, (recOwn j hj).2.1]
    have perm : cs.toList.Perm (recs.toList.map MutConst.recr) := by
      rw [hcs]
      refine (List.perm_ext_iff_of_nodup ?_ nodupX).mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
      · exact filterMap_nodup Std.HashSet.distinct_toList fun a b x ha hb =>
          BEq.trans (BEq.symm (memberOf_name namedE ha)) (memberOf_name namedE hb)
      · obtain ⟨x, hx, hxm⟩ := List.mem_filterMap.mp hm
        obtain ⟨j, hj, e⟩ := (memAll x).mp (contains_of_listed hx)
        rw [← memberOf_congr envCongr e, recMember j hj] at hxm
        cases hxm
        exact List.mem_map.mpr ⟨recs[j], Array.mem_toList_iff.mpr (Array.getElem_mem hj), rfl⟩
      · obtain ⟨rv, hrv, rfl⟩ := List.mem_map.mp hm
        obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hrv)
        obtain ⟨x, hx, e⟩ := listed ((memAll _).mpr ⟨j, hj, BEq.rfl⟩)
        exact List.mem_filterMap.mpr ⟨x, hx, by rw [← memberOf_congr envCongr e, recMember j hj]⟩
    rw [LeanOrder.sourceClasses_eq perm sortedX noTieX] at hout
    exact hout

/-! ## In the segment theorems' forms -/

/-- **A fold block's run claims its records** (`TraceSegments.Claimed`). -/
theorem FoldBlock.claimed {env sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {snap : DriverAcc}
    {rep : Ix.Name} {all : Ix.Set Ix.Name} {r : BlockResult} {c : BlockState}
    (fb : FoldBlock env sub ixe failures snap rep all r c) {out : BlockResult}
    (hrec : BlockRecords.recordsOf r = BlockRecords.recordsOf out) : TraceSegments.Claimed ixe sub out :=
  ⟨snap.cenv, all, blockKey rep all, r, c, fb.ran, fb.published, hrec⟩

/-- **The blobs a run reads are the artifact's** (`TraceSegments.BlobsKept`), for a run to a state
whose blobs the fold block's final state keeps. -/
theorem FoldBlock.blobsKept {env sub : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {snap : DriverAcc}
    {rep : Ix.Name} {all : Ix.Set Ix.Name} {r : BlockResult} {c : BlockState}
    (fb : FoldBlock env sub ixe failures snap rep all r c) {after : BlockState}
    (ext : BlobWrites.Extends snap.cenv.blobs after c) : TraceSegments.BlobsKept ixe snap.cenv after :=
  fun a v h => fb.blobs a v (ext a v h)

/-- **`BlockCompiled.ran`, `.claimed` and `.blobs`** for a definitions group of two or more, at the
fold's block of the group (`FoldBlock`, which also gives `fresh`, `bound` and `published`). -/
theorem definitions_compiled {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint}
    (scheduled : ∀ x ∈ (Ix.LeanIngress.scheduleOf (quotientGraph ixe t hints sub)).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    {i : Nat} {members : Array Ix.ConstantInfo}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.definitions members)) (two : 2 ≤ members.size) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      (∀ d ∈ TraceSegments.defsOf members, all.contains d.name = true) ∧
      ∃ out after, rawRun (compileMutualBlock (((TraceSegments.defsOf members).map MutConst.defn).map ([·])))
          (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
          (.ok out, after) ∧
        TraceSegments.Claimed ixe sub out ∧ TraceSegments.BlobsKept ixe snap.cenv after := by
  obtain ⟨snap, rep, all, r, c, fb, mem, out, after, ran, ext, hrec⟩ := definitions_run P scheduled hgr two
  exact ⟨snap, rep, all, r, c, fb, mem, out, after, ran, fb.claimed hrec, fb.blobsKept ext⟩

/-- **`InductiveCompiled.ran₁`, `.claimed₁` and `.blobs₁`**: an inductive group's types, at the
fold's block of its types. -/
theorem types_compiled {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fbk : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc)) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      ∃ out after, rawRun (compileMutualBlock (((indsOf types ctors).map MutConst.indc).map ([·])))
          (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
          (.ok out, after) ∧
        TraceSegments.Claimed ixe sub out ∧ TraceSegments.BlobsKept ixe snap.cenv after := by
  obtain ⟨snap, rep, all, r, c, fb, -, out, after, ran, ext, hrec⟩ := types_run P fbk hgr distinct
  exact ⟨snap, rep, all, r, c, fb, out, after, ran, fb.claimed hrec, fb.blobsKept ext⟩

/-- **`InductiveCompiled.family` and `.blobs₂`**: an inductive group's recursors, at the fold's
block of its recursors, with `cenv₂ := snap.cenv`. -/
theorem recursors_family {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (fbk : FamilyBlocks env)
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {i : Nat}
    {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)} {recs : Array Ix.RecursorVal}
    (hgr : (quotientGraph ixe t hints sub).groups[i]? = some (.inductive types ctors recs))
    (distinct : Canon.KeysDistinct ((indsOf types ctors).map MutConst.indc)) :
    ∃ snap rep all r c, FoldBlock env sub ixe failures snap rep all r c ∧
      ∃ out after,
        (∃ (cenvR₂ : CompileEnv) (all₂ : Ix.Set Ix.Name) (key₂ : Ix.Name) (r₂ : BlockResult) (cache₂ : BlockState),
          runBlock cenvR₂ all₂ key₂ = .ok (r₂, cache₂) ∧ BlockPublication.Published ixe sub key₂ r₂ ∧
          BlockRecords.recordsOf r₂ = BlockRecords.recordsOf out ∧
          (rawRun (compileMutualBlock ((recs.toList.map MutConst.recr).map ([·])))
              (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
              (.ok out, after) ∨
            ∃ r', recs.toList = [r'] ∧ key₂ = r'.cnst.name ∧
              rawRun (compileConstantInfo (.recInfo r'))
                (snap.cenv, { all, current := blockKey rep all, mutCtx := default, univCtx := [] }) {} =
                (.ok out, after))) ∧
        TraceSegments.BlobsKept ixe snap.cenv after := by
  obtain ⟨snap, rep, all, r, c, fb, -, out, after, ran, ext, hrec⟩ := recursors_run P fbk hgr distinct
  exact ⟨snap, rep, all, r, c, fb, out, after, ⟨snap.cenv, all, blockKey rep all, r, c, fb.ran, fb.published, hrec,
    ran⟩, fb.blobsKept ext⟩

end Ix.Cert.GroupRuns

/-- info: 'Ix.Cert.GroupRuns.definitions_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.GroupRuns.definitions_compiled

/-- info: 'Ix.Cert.GroupRuns.types_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.GroupRuns.types_compiled

/-- info: 'Ix.Cert.GroupRuns.recursors_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.GroupRuns.recursors_family
