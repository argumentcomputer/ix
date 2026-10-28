import Ix.Cert.GroupRuns
import Ix.Cert.StepsEncode
import Ix.Cert.BindingsResolve

/-! # A stored definition projection's block is a stored block record

The reader takes a definition's hint at its member reference (`Ix.Cert.hintsOf`): at the
member's projection record, or at the member's block address when no stored projection record
projects the member. This module shows that a stored definition projection names, as its block,
an address whose stored record is a block record (`.muts`) (`projections_owned`). So no stored
projection projects a lone record's member 0 (`no_projection_of_lone`), and a singleton's hint is
read at its own record.

The fold keeps it (`reach_owned`): a block the fold merges is checked against the store and
against itself (`checkCompiledBlock`'s content check, `Resolution.Agrees`), so the merge only
adds records; it stores its block record before its projections; and a block with a projection
that is not the block itself was built from `.muts` payloads, which the canonical sharing keeps
(`runBlock_rows`). -/

namespace Ix.Cert.ProjectionOwners

open Ix.CompileM Ix.CompileCert Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Cert.BindingsResolve (storeOf storeOf_mono storeOf_ser)
open Ix.Cert.BlockLayout (ResultShape ProjectsTo Built)

/-! ## The rows of a compiled block -/

/-- The canonical sharing keeps a block's info a block's. -/
theorem built_muts {limits : Ix.Sharing.Exact.Limits} {ms : Array Ixon.MutConst} {refs : Array Address}
    {univs : Array Ixon.Univ} {out : Ixon.Constant}
    (ran : buildConstantWithSharing limits (.muts ms) refs univs = .ok out) : ∃ ms', out.info = .muts ms' := by
  have erased := (SharingRoots.build_roots (md := .anon) limits (.muts ms) refs univs out ran).1
  cases hi : out.info <;> simp_all [SharingRoots.erase, Ix.Sharing.Exact.mapRoots]

/-- **A mutual build's rows are its block, or its block is a block record.** -/
theorem buildMutual_rows {limits : Ix.Sharing.Exact.Limits} {classes : List (List MutConst)}
    {payloads : Array Ixon.MutConst} {metas : Array (Ix.Name × Ixon.ConstantMeta)} {cache : BlockState}
    {out : BlockResult} (ran : buildCompiledMutualBlock limits classes payloads metas cache = .ok out) :
    (∀ p ∈ out.projections, p.2.1 = out.block) ∨ ∃ ms, out.block.info = .muts ms := by
  unfold buildCompiledMutualBlock at ran
  cases hs : standaloneMutConstInfo? payloads with
  | some info =>
    rw [hs] at ran
    obtain ⟨block, -, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    refine .inl fun p hp => ?_
    have logical : (p.1, p.2.1) ∈ MutualProjections.logicalRows
        (buildStandaloneMutualProjections classes block metas) :=
      List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩
    rw [MutualProjections.standalone_rows] at logical
    obtain ⟨_, _, e⟩ := List.mem_map.mp logical
    exact (Prod.mk.inj e).2.symm
  | none =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact .inr (built_muts hb)

/-- `buildMutual_rows` for the mutual block compile. -/
theorem compileMutualBlock_rows (classes : List (List MutConst)) :
    BlockRecords.Returns (fun out : BlockResult => (∀ p ∈ out.projections, p.2.1 = out.block) ∨
      ∃ ms, out.block.info = .muts ms) (compileMutualBlock classes) := by
  intro ctx s x s' ran
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, _, -, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨_, _, -, finished⟩ := bind_ok compiled
  exact buildMutual_rows (ProjectionLayout.finish_mutual_ok _ _ _ _ finished).2.2

/-- **A compiled block's rows are its block, or its block is a block record**: a lone
constant's compile has no rows (`ClosureResolve.constantInfo_lone`), and a mutual compile's are
`buildMutual_rows`'. -/
theorem runBlock_rows {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {c : BlockState} (hr : runBlock cenv all lo = .ok (r, c)) :
    (∀ p ∈ r.projections, p.2.1 = r.block) ∨ ∃ ms, r.block.info = .muts ms := by
  obtain ⟨const, -, paths⟩ := GroupRuns.runBlock_paths hr
  rcases paths with ⟨hcond, hs⟩ | ⟨-, cs, out, s₄, -, hout, -, hrec⟩
  · have hi : ∀ v, const = .inductInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    have hc : ∀ v, const = .ctorInfo v → False := by
      rintro v rfl
      simp [GroupRuns.isIndConst] at hcond
    obtain ⟨hproj, -⟩ := ClosureResolve.constantInfo_lone const hi hc _ _ _ _ hs
    exact .inl fun p hp => by rw [hproj] at hp; simp at hp
  · simp only [BlockRecords.recordsOf, Prod.mk.injEq] at hrec
    obtain ⟨hblock, -, -, hrows⟩ := hrec
    rcases compileMutualBlock_rows _ _ _ _ _ hout with rows | muts
    · refine .inl fun p hp => ?_
      have hm : (p.1, p.2.1) ∈ out.projections.map fun p => (p.1, p.2.1) := by
        rw [← hrows]
        exact Array.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨q, hq, e⟩ := Array.mem_map.mp hm
      rw [← (Prod.mk.inj e).2, hblock]
      exact rows q hq
    · exact .inr (by rw [hblock]; exact muts)

/-- A built constant is no definition projection. -/
theorem built_not_dPrj {c : Ixon.Constant} (h : Built c) {p : Ixon.DefinitionProj} : c.info ≠ .dPrj p := by
  intro hi
  have h1 := h.owner ⟨⟨#[]⟩⟩
  have h2 := h.owner ⟨⟨#[0]⟩⟩
  simp only [ownerOf, hi] at h1 h2
  have apart : (⟨⟨#[]⟩⟩ : Address) ≠ ⟨⟨#[0]⟩⟩ := fun e => by
    have := congrArg (fun a : Address => a.hash.size) e
    exact absurd this (by decide)
  exact apart (h1.symm.trans h2)

/-! ## The fold keeps every stored definition projection's block a block record -/

/-- **Every stored definition projection names a stored block record as its block.** -/
def Owned (store : Std.HashMap Address ByteArray) : Prop :=
  ∀ a c p, storeOf store a = some c → c.info = .dPrj p → ∃ m ms, storeOf store p.block = some m ∧ m.info = .muts ms

theorem owned_empty : Owned {} := fun a c p h => by
  simp [storeOf, Std.HashMap.get?_eq_getElem?] at h

/-- An insert at a fresh address, or with the bytes already there, only adds. -/
theorem insert_grows {store : Std.HashMap Address ByteArray} {k : Address} {v : ByteArray}
    (h : ∀ v₀, store.get? k = some v₀ → v₀ = v) :
    ∀ a b, store.get? a = some b → (store.insert k v).get? a = some b := by
  intro a b hb
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  split
  · rename_i same
    have e : k = a := beq_iff_eq.mp same
    subst e
    rw [h b hb]
  · rw [← Std.HashMap.get?_eq_getElem?]
    exact hb

/-- What the merge of a checked block keeps of its store, insert by insert: the projections'
blocks, agreement with the block's writes, and its block record. -/
def MergeInv (W : List (Address × ByteArray)) (B : Address) (bytes : ByteArray)
    (store : Std.HashMap Address ByteArray) : Prop :=
  Owned store ∧ (∀ k v, (k, v) ∈ W → ∀ v₀, store.get? k = some v₀ → v₀ = v) ∧ store.get? B = some bytes

theorem mergeInv_insert {W : List (Address × ByteArray)}
    {store : Std.HashMap Address ByteArray} (own : ∀ k v v', (k, v) ∈ W → (k, v') ∈ W → v = v')
    (hI : Owned store) (cons : ∀ k v, (k, v) ∈ W → ∀ v₀, store.get? k = some v₀ → v₀ = v)
    {k : Address} {c : Ixon.Constant} (hk : (k, Ixon.ser c) ∈ W) (wire : c.wireWF)
    (proj : ∀ p, c.info = .dPrj p → ∃ m ms, storeOf (store.insert k (Ixon.ser c)) p.block = some m ∧
      m.info = .muts ms) :
    Owned (store.insert k (Ixon.ser c)) ∧
      ∀ k' v, (k', v) ∈ W → ∀ v₀, (store.insert k (Ixon.ser c)).get? k' = some v₀ → v₀ = v := by
  have grows := insert_grows (cons k _ hk)
  refine ⟨fun a c' p ha hp => ?_, fun k' v hv v₀ h₀ => ?_⟩
  · by_cases e : a = k
    · subst e
      have hser : (store.insert a (Ixon.ser c)).get? a = some (Ixon.ser c) := by
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
      rw [storeOf_ser wire hser] at ha
      cases ha
      exact proj p hp
    · have ha' : storeOf store a = some c' := by
        unfold storeOf at ha ⊢
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at ha
        split at ha
        · rename_i same
          exact absurd (beq_iff_eq.mp same).symm e
        · rw [Std.HashMap.get?_eq_getElem?]
          exact ha
      obtain ⟨m, ms, hm, hms⟩ := hI a c' p ha' hp
      exact ⟨m, ms, storeOf_mono grows _ _ hm, hms⟩
  · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h₀
    split at h₀
    · rename_i same
      have e : k = k' := beq_iff_eq.mp same
      subst e
      cases h₀
      exact own _ _ _ hk hv
    · exact cons k' v hv v₀ (by rw [Std.HashMap.get?_eq_getElem?]; exact h₀)

/-- **A checked merge keeps every stored definition projection's block a block record.** -/
theorem merge_owned {acc : DriverAcc} {lo : Ix.Name} {cenv : CompileEnv} {all : Ix.Set Ix.Name}
    {key : Ix.Name} {r : BlockResult} {cache c' : BlockState} (hr : runBlock cenv all key = .ok (r, c'))
    (hchk : checkAnonymousWrites acc.cenv.constants (blockRecordWrites r) = true)
    (hI : Owned acc.cenv.constants) : Owned (mergeCompiledBlock acc lo r cache).cenv.constants := by
  have ag := checkAnonymousWrites_agrees hchk
  have shape := BlockLayout.runBlock_shape hr
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
  have rows := runBlock_rows hr
  have hbW : (r.blockAddr, Ixon.ser r.block) ∈ blockRecordWrites r := by
    rw [← shape.bytes]; exact write_block
  refine (StepsEncode.mergeCompiledBlock_constants (MergeInv (blockRecordWrites r) r.blockAddr r.blockBytes)
    ?_ ?_).1
  · have step := mergeInv_insert ag.own hI ag.old hbW wire fun p hp =>
      (built_not_dPrj shape.built hp).elim
    rw [← shape.bytes] at step
    refine ⟨step.1, step.2, ?_⟩
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
  · intro p hp s ⟨hI', cons, hB⟩
    have hpW : (Address.admissionHash (Ixon.ser p.2.1), Ixon.ser p.2.1) ∈ blockRecordWrites r := write_projection hp
    have pwire : p.2.1.wireWF := by
      rcases shape.rows p hp with same | ⟨pw, -, -⟩
      · rw [same]; exact wire
      · exact pw
    have grows := insert_grows (cons _ _ hpW)
    have step := mergeInv_insert ag.own hI' cons hpW pwire fun q hq => by
      rcases shape.rows p hp with same | ⟨-, -, owner⟩
      · rw [same] at hq
        exact (built_not_dPrj shape.built hq).elim
      · have hqb : q.block = r.blockAddr := by
          have := owner ⟨⟨#[]⟩⟩
          simp only [ownerOf, hq] at this
          exact this
        rcases rows with same | muts
        · rw [same p hp] at hq
          exact (built_not_dPrj shape.built hq).elim
        · obtain ⟨ms, hms⟩ := muts
          refine ⟨r.block, ms, ?_, hms⟩
          rw [hqb]
          exact storeOf_ser wire (by rw [← shape.bytes]; exact grows _ _ hB)
    exact ⟨step.1, step.2, grows _ _ hB⟩

/-- **Every state the fold reaches keeps every stored definition projection's block a block
record**, from an empty store. -/
theorem reach_owned {blocks : Ix.CondensedBlocks} {init : DriverAcc} (start : Owned init.cenv.constants) :
    ∀ {acc : DriverAcc}, Reach blocks init acc → Owned acc.cenv.constants := by
  intro acc h
  induction h with
  | init => exact start
  | @step snap acc rep all _ _ _ _ _ ih =>
    refine StepsEncode.applyAuxBlockOutcome_constants Owned acc _ all _ ih fun r c ho hc => ?_
    exact merge_owned (auxBlockOutcome_compiled ho) (checkCompiledBlock_content hc) ih

/-! ## In the artifact -/

/-- **The fold behind a compile, with its store both ways**: `StoredEncoding.compileReport_start`,
and every record of the final state's store is the artifact's, as its own buffer. -/
theorem compileReport_store {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) :
    ∃ (cenv₀ : CompileEnv) (sched : FoldSchedule) (st : FoldState),
      StoredEncoding.FoldStart env cenv₀ ∧
      foldWavesSeq (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched
        ((Ix.CondenseM.run (groundSplit { consts := env.consts }).1).blocks.size + 1)
        (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1) sched) = .ok st ∧
      (∀ a lc, ixe.consts.get? a = some lc →
        ∃ b, st.acc.cenv.constants.get? a = some b ∧ lc = { buf := b, len := b.size }) ∧
      ∀ a b, st.acc.cenv.constants.get? a = some b → ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨cenv, hu, -⟩ := compileReport_ok h
  obtain ⟨bytes, hf⟩ := compileUnchecked_fold hu
  rw [compileEnvFold_eq_seq] at hf
  unfold compileEnvFoldSeq at hf
  generalize missingBlockRefs? _ = missing at hf
  generalize validateInductiveFlags _ = flags at hf
  generalize validateMutualSafety _ _ = safety at hf
  cases missing <;> cases flags <;> cases safety <;>
    simp only [bind, Except.bind, pure, Except.pure] at hf <;> try cases hf
  generalize hr : foldWavesSeq _ _ _ _ = r at hf
  cases r with
  | error => cases hf
  | ok st =>
    simp only [finalizeEnv, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, -, -⟩ := hf
    exact ⟨_, _, st, ⟨rfl, rfl, rfl⟩, hr, fun a lc hlc => StoredEncoding.assembleEnv_consts_inv _ hlc,
      fun a b hb => assembleEnv_consts _ hb⟩

/-- **A stored definition projection names a stored block record as its block.** -/
theorem projections_owned {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) {a : Address} {c : Ixon.Constant} {p : Ixon.DefinitionProj}
    (hc : recordAt ixe a = some c) (hp : c.info = .dPrj p) :
    ∃ m ms, recordAt ixe p.block = some m ∧ m.info = .muts ms := by
  obtain ⟨cenv₀, sched, st, h₀, hst, toStore, ofStore⟩ := compileReport_store h
  have start : Owned (FoldState.init cenv₀ (Ix.CondenseM.run (groundSplit { consts := env.consts }).1)
      sched).acc.cenv.constants := by
    show Owned cenv₀.constants
    rw [h₀.constants]
    exact owned_empty
  have hreach := foldWavesSeq_reach _ _ _ hst (Reach.init (blocks := Ix.CondenseM.run
    (groundSplit { consts := env.consts }).1) (init := (FoldState.init cenv₀ _ sched).acc))
  have owned := reach_owned start hreach
  -- the artifact's record at `a` is the final store's
  have hsa : storeOf st.acc.cenv.constants a = some c := by
    unfold recordAt at hc
    cases hla : ixe.consts.get? a with
    | none => rw [hla] at hc; cases hc
    | some lc =>
      rw [hla] at hc
      obtain ⟨b, hb, rfl⟩ := toStore a lc hla
      unfold storeOf
      rw [hb]
      exact hc
  obtain ⟨m, ms, hm, hms⟩ := owned a c p hsa hp
  refine ⟨m, ms, ?_, hms⟩
  unfold storeOf at hm
  cases hb : st.acc.cenv.constants.get? p.block with
  | none => rw [hb] at hm; cases hm
  | some b =>
    rw [hb] at hm
    unfold recordAt
    rw [ofStore _ _ hb]
    exact hm

/-- **No stored definition projection projects a lone record's member**: its block would be a
block record at the lone record's address. -/
theorem no_projection_of_lone {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) {B : Address} {c : Ixon.Constant}
    (hB : recordAt ixe B = some c) (lone : BlockContext.lone c.info = true) (k : Nat) :
    ∀ e ∈ ixe.consts.toList, ∀ a', CtxAgree.projEntry e ≠ some (.member B k, a') := by
  intro e he a' hpe
  obtain ⟨block, index, same, hp⟩ := CtxAgree.projEntry_eq_some.mp hpe
  unfold definitionProjection at hp
  cases hget : e.2.get? with
  | none => rw [hget] at hp; cases hp
  | some c' =>
    rw [hget] at hp
    dsimp only at hp
    split at hp
    · rename_i p hinfo
      cases hp
      cases same
      have hrec : recordAt ixe e.1 = some c' := by
        unfold recordAt
        rw [Std.HashMap.get?_eq_getElem?, (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he)]
        exact hget
      obtain ⟨m, ms, hm, hms⟩ := projections_owned h hrec hinfo
      rw [hB] at hm
      cases hm
      rw [hms] at lone
      cases lone
    · cases hp

end Ix.Cert.ProjectionOwners

/-- info: 'Ix.Cert.ProjectionOwners.projections_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.ProjectionOwners.projections_owned

/-- info: 'Ix.Cert.ProjectionOwners.no_projection_of_lone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.ProjectionOwners.no_projection_of_lone
