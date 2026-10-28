import Ix.Cert.ClosureLayout
import Ix.Cert.StoredEncoding
import Ix.Cert.BlockRecords
import Ix.CompileCert.MutualProjections
import Ix.CompileCert.ProjectionLayout
import Ix.Ixon.Authenticated.Theorems

/-! # A compiled block's records, as `Layout.block` reads them

Every block the compiler returns has one shape (`ResultShape`): its block record is a constant
the canonical sharing built (`Built`: never a projection), stored as its serialization at the
serialization's admission hash, and every row it registers a name at is the block itself or a
projection of the block (`ProjectsTo`). A name's published record is a primary claim of its
block's `runBlock`, so its record decodes, and its block decodes to the built block, a
non-projection (`claim_block`): what `ClosureLayout.Layout.block` asks of a group's names
(`layoutBlock_of_claimed`).

Decoding a record to the constant it serializes needs the constant in the wire domain. For a
projection that is proved (`MutualProjections`); for the built block it is the premise
`BlocksWire`, stated here once. -/

namespace Ix.Cert.BlockLayout

open Ix.CompileM Ix.CompileCert
open Ix.Cert.ClosureLayout (blockAt addrOf)
open Ix.Cert.BlockRecords (Returns)

/-- **Every block the compiler returns is in the wire domain.** Not `buildConstantWithSharing`'s
wire validity for arbitrary tables: the builder passes the reference and universe tables through,
so its output is wire-valid only for wire-valid tables (`Ix.Sharing.Verify.BlockWireTablesWF`, which
the compile keeps from its empty start, `EmissionWire.Safe`) and a well-formed header
(`ConstantInfoHeaderWF`). -/
def BlocksWire : Prop :=
  ∀ (cenv : CompileEnv) (all : Ix.Set Ix.Name) (lo : Ix.Name) (r : BlockResult) (c : BlockState),
    runBlock cenv all lo = .ok (r, c) → r.block.wireWF

/-- An info that is no projection. -/
def NotPrj : Ixon.ConstantInfo → Prop
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ => False
  | _ => True

/-- A constant the canonical sharing built from an info that is no projection. -/
def Built (c : Ixon.Constant) : Prop :=
  ∃ limits info refs univs, buildConstantWithSharing limits info refs univs = .ok c ∧ NotPrj info

/-- A projection of the block at `owner`, in the wire domain. -/
def ProjectsTo (owner : Address) (c : Ixon.Constant) : Prop :=
  c.wireWF ∧ ∀ a, ownerOf a c = owner

/-- **A compiled block's shape.** -/
structure ResultShape (r : BlockResult) : Prop where
  bytes : r.blockBytes = Ixon.ser r.block
  addr : r.blockAddr = Address.admissionHash r.blockBytes
  built : Built r.block
  rows : ∀ p ∈ r.projections, p.2.1 = r.block ∨ ProjectsTo r.blockAddr p.2.1

/-- A built constant is no projection. -/
theorem Built.owner {c : Ixon.Constant} (h : Built c) (a : Address) : ownerOf a c = a := by
  obtain ⟨limits, info, refs, univs, ran, hinfo⟩ := h
  obtain ⟨erased, -⟩ := SharingRoots.build_roots (md := .anon) limits info refs univs c ran
  unfold ownerOf
  split
  all_goals first
    | rfl
    | (rename_i p hp
       rw [hp] at erased
       cases info <;> simp_all [SharingRoots.erase, Ix.Sharing.Exact.mapRoots, NotPrj])

theorem buildBlockConstant_ok {info : Ixon.ConstantInfo} {refs : Array Address} {univs : Array Ixon.Univ}
    {ctx : CompileEnv × BlockEnv} {s s' : BlockState} {c : Ixon.Constant}
    (h : rawRun (buildBlockConstant info refs univs) ctx s = (.ok c, s')) :
    buildConstantWithSharing ctx.1.sharingLimits info refs univs = .ok c := by
  unfold buildBlockConstant at h
  obtain ⟨env, mid, hread, h⟩ := bind_ok h
  have hr : rawRun (read : CompileM (CompileEnv × BlockEnv)) ctx s = (.ok ctx, s) := rfl
  rw [hr] at hread
  cases hread
  unfold liftSharing at h
  cases hb : buildConstantWithSharing ctx.1.sharingLimits info refs univs with
  | ok c' =>
    rw [hb] at h
    rw [rawRun_pure] at h
    cases h
    rfl
  | error e =>
    rw [hb] at h
    cases h

theorem Returns.withBlockEnv {α : Type} {P : α → Prop} {f : BlockEnv → BlockEnv} {m : CompileM α}
    (h : Returns P m) : Returns P (withBlockEnv f m) := by
  intro ctx s x s' ran
  rw [rawRun_withBlockEnv] at ran
  exact h _ _ _ _ ran

theorem finishConstant_shape {info : Ixon.ConstantInfo} (hinfo : NotPrj info) (blockMeta : Ixon.ConstantMeta) :
    Returns ResultShape (finishConstantInfoWithSharing info blockMeta) := by
  intro ctx s x s' ran
  unfold finishConstantInfoWithSharing finishConstantWithSharing at ran
  obtain ⟨cache, mid, -, ran⟩ := bind_ok ran
  obtain ⟨block, mid', hb, ran⟩ := bind_ok ran
  rw [rawRun_pure] at ran
  cases ran
  exact ⟨rfl, rfl, ⟨_, _, _, _, buildBlockConstant_ok hb, hinfo⟩, fun p hp => by simp [BlockResult.mk'] at hp⟩

theorem inductiveProjections_rows (i : Ix.InductiveVal) (indMeta : Ixon.ConstantMeta)
    (pairs : Array (Ix.Name × Ixon.ConstantMeta)) (addr : Address) (width : addr.hash.size = 32) :
    ∀ p ∈ buildInductiveProjections i indMeta pairs addr, ProjectsTo addr p.2.1 := by
  intro p hp
  unfold buildInductiveProjections at hp
  rcases Array.mem_append.mp hp with hp | hp
  · simp only [List.mem_toArray, List.mem_singleton] at hp
    subst hp
    exact ⟨MutualProjections.empty_tables_wire _ width, fun _ => rfl⟩
  · obtain ⟨k, hk, rfl⟩ := Array.mem_mapIdx.mp hp
    exact ⟨MutualProjections.empty_tables_wire _ width, fun _ => rfl⟩

theorem finishInductive_shape (i : Ix.InductiveVal) (ind : Ixon.Inductive) (indMeta : Ixon.ConstantMeta)
    (pairs : Array (Ix.Name × Ixon.ConstantMeta)) :
    Returns ResultShape (finishInductiveFamilyBlock i ind indMeta pairs) := by
  intro ctx s x s' ran
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨_, _, -, ran⟩ := bind_ok ran
  obtain ⟨_, _, -, ran⟩ := bind_ok ran
  obtain ⟨cache, mid, -, ran⟩ := bind_ok ran
  obtain ⟨block, mid', hb, ran⟩ := bind_ok ran
  rw [rawRun_pure] at ran
  cases ran
  refine ⟨rfl, rfl, ⟨_, _, _, _, buildBlockConstant_ok hb, trivial⟩, fun p hp => .inr ?_⟩
  exact inductiveProjections_rows i indMeta pairs _ (Ixon.Authenticated.admissionHash_width _) p hp

theorem mutualProjections_rows (classes : List (List MutConst)) (owner : Address) (width : owner.hash.size = 32)
    (metas : Array (Ix.Name × Ixon.ConstantMeta)) :
    ∀ p ∈ buildMutualProjections classes owner metas, ProjectsTo owner p.2.1 := by
  intro p hp
  refine ⟨MutualProjections.build_rows_wire classes owner width metas p hp, fun a => ?_⟩
  have logical : (p.1, p.2.1) ∈ MutualProjections.logicalRows (buildMutualProjections classes owner metas) :=
    List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩
  rw [MutualProjections.build_rows, MutualProjections.expectedRows] at logical
  obtain ⟨⟨members, index⟩, _, inClass⟩ := List.mem_flatMap.mp logical
  obtain ⟨source, _, generated⟩ := List.mem_flatMap.mp inClass
  unfold MutualProjections.sourceRows at generated
  rcases List.mem_cons.mp generated with e | rest
  · have : p.2.1 = MutualProjections.memberProjection owner index.toUInt64 source := (Prod.mk.inj e).2
    rw [this]
    cases source <;> rfl
  · obtain ⟨⟨ctor, ctorIndex⟩, _, e⟩ := List.mem_map.mp rest
    have : p.2.1 = MutualProjections.constructorProjection owner index.toUInt64 ctorIndex.toUInt64 :=
      (Prod.mk.inj e).2.symm
    rw [this]
    rfl

theorem standalone_notPrj (payloads : Array Ixon.MutConst) {info : Ixon.ConstantInfo}
    (h : standaloneMutConstInfo? payloads = some info) : NotPrj info := by
  rcases payloads with ⟨l⟩
  rcases l with _ | ⟨m, _ | ⟨m₂, rest⟩⟩
  · cases h
  · cases m with
    | defn d => cases h; trivial
    | indc i => cases h
    | recr r => cases h; trivial
  · cases h

theorem buildMutual_shape {limits : Ix.Sharing.Exact.Limits} {classes : List (List MutConst)}
    {payloads : Array Ixon.MutConst} {metas : Array (Ix.Name × Ixon.ConstantMeta)} {cache : BlockState}
    {out : BlockResult} (ran : buildCompiledMutualBlock limits classes payloads metas cache = .ok out) :
    ResultShape out := by
  unfold buildCompiledMutualBlock at ran
  cases hs : standaloneMutConstInfo? payloads with
  | some info =>
    rw [hs] at ran
    obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    have hinfo : NotPrj info := standalone_notPrj payloads hs
    refine ⟨rfl, rfl, ⟨_, _, _, _, hb, hinfo⟩, fun p hp => .inl ?_⟩
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
    exact ⟨rfl, rfl, ⟨_, _, _, _, hb, trivial⟩, fun p hp => .inr
      (mutualProjections_rows classes _ (Ixon.Authenticated.admissionHash_width _) metas p hp)⟩

/-- **A mutual block compile returns a block of this shape.** -/
theorem compileMutualBlock_shape (classes : List (List MutConst)) :
    Returns ResultShape (compileMutualBlock classes) := by
  intro ctx s x s' ran
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, _, -, compiled⟩ := bind_ok ran
  unfold compileMutualPayload at compiled
  obtain ⟨_, _, -, finished⟩ := bind_ok compiled
  exact buildMutual_shape (ProjectionLayout.finish_mutual_ok _ _ _ _ finished).2.2

theorem defnBlock_shape (d : Ix.Def) : Returns ResultShape (compileDefinitionDataInfo d) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  exact Returns.bind fun _ => Returns.bind fun _ => (by refine finishConstant_shape ?_ _; exact trivial)

theorem inductiveInfo_shape (v : Ix.InductiveVal) : Returns ResultShape (compileInductiveInfo v) := by
  unfold compileInductiveInfo
  refine Returns.bind fun _ => Returns.withBlockEnv ?_
  unfold compileInductiveFamilyInfo compileInductiveFamilyBlock
  exact Returns.bind fun _ => Returns.bind fun _ => finishInductive_shape _ _ _ _

/-- **A lone constant's compile returns a block of this shape.** -/
theorem compileConstantInfo_shape (const : Ix.ConstantInfo) :
    Returns ResultShape (compileConstantInfo const) := by
  cases const with
  | defnInfo v =>
    unfold compileConstantInfo compileDefinitionConstantInfo withMutCtx
    refine Returns.withBlockEnv ?_
    unfold compileDefinitionInfo compileDefinitionBlock
    exact Returns.bind fun _ => Returns.bind fun _ => (by refine finishConstant_shape ?_ _; exact trivial)
  | thmInfo v =>
    unfold compileConstantInfo compileTheoremConstantInfo withMutCtx
    exact Returns.withBlockEnv (defnBlock_shape _)
  | opaqueInfo v =>
    unfold compileConstantInfo compileOpaqueConstantInfo withMutCtx
    exact Returns.withBlockEnv (defnBlock_shape _)
  | quotInfo v =>
    unfold compileConstantInfo compileQuotientConstantInfo withMutCtx
    refine Returns.withBlockEnv ?_
    unfold compileQuotientInfo compileQuotientBlock
    exact Returns.bind fun _ => Returns.bind fun _ => (by refine finishConstant_shape ?_ _; exact trivial)
  | recInfo v =>
    unfold compileConstantInfo compileRecursorConstantInfo withMutCtx
    refine Returns.withBlockEnv ?_
    unfold compileRecursorInfo compileRecursorBlock
    exact Returns.bind fun _ => Returns.bind fun _ => (by refine finishConstant_shape ?_ _; exact trivial)
  | inductInfo v =>
    unfold compileConstantInfo compileInductiveConstantInfo withMutCtx
    exact Returns.withBlockEnv (inductiveInfo_shape v)
  | ctorInfo v =>
    unfold compileConstantInfo compileConstructorConstantInfo withMutCtx
    refine Returns.withBlockEnv ?_
    unfold compileConstructorInfo
    refine Returns.bind fun c => ?_
    split
    · exact inductiveInfo_shape _
    · intro ctx s x s' ran
      cases ran
  | axiomInfo v =>
    unfold compileConstantInfo compileConstantInfoCore withMutCtx
    refine Returns.withBlockEnv ?_
    unfold compileAxiomInfo compileAxiomBlock
    exact Returns.bind fun _ => Returns.bind fun _ => (by refine finishConstant_shape ?_ _; exact trivial)

/-- **A block `runBlock` returns has this shape**: its records are a lone constant's or a mutual
block's compile's. -/
theorem runBlock_shape {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {c : BlockState} (h : runBlock cenv all lo = .ok (r, c)) :
    ResultShape r := by
  obtain ⟨const, -, rest⟩ := BlockRecords.runBlock_records h
  have transfer : ∀ out, ResultShape out → BlockRecords.recordsOf r = BlockRecords.recordsOf out → ResultShape r := by
    intro out shape same
    simp only [BlockRecords.recordsOf, Prod.mk.injEq] at same
    obtain ⟨hblock, hbytes, haddr, hrows⟩ := same
    refine ⟨by rw [hbytes, hblock]; exact shape.bytes, by rw [haddr, hbytes]; exact shape.addr,
      by rw [hblock]; exact shape.built, fun p hp => ?_⟩
    have hm : (p.1, p.2.1) ∈ out.projections.map fun p => (p.1, p.2.1) := by
      rw [← hrows]; exact Array.mem_map.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, e⟩ := Array.mem_map.mp hm
    have he : q.2.1 = p.2.1 := (Prod.mk.inj e).2
    rw [hblock, haddr, ← he]
    exact shape.rows q hq
  rcases rest with ⟨r', s₂, run, same⟩ | ⟨cs, out, s₄, run, same⟩
  · exact transfer r' (compileConstantInfo_shape const _ _ _ _ run) same
  · exact transfer out (compileMutualBlock_shape _ _ _ _ _ run) same

/-! ## `Layout.block` -/

/-- **What the fold says of a published closure name's record**: a primary claim of a block
`runBlock` returned, the block's own record stored too. -/
def ClaimedAt (ixe : Ixon.Env) (n : Ix.Name) (a : Address) : Prop :=
  ∃ (cenv : CompileEnv) (A : Ix.Set Ix.Name) (k : Ix.Name) (r : BlockResult) (c : BlockState)
    (b : ByteArray),
    runBlock cenv A k = .ok (r, c) ∧ (n, a, b) ∈ Resolution.claimWrites k r ∧
    ixe.consts.get? a = some { buf := b, len := b.size } ∧
    ixe.consts.get? r.blockAddr = some { buf := r.blockBytes, len := r.blockBytes.size }

theorem recordAt_ser {ixe : Ixon.Env} {a : Address} {c : Ixon.Constant} (wire : c.wireWF)
    (h : ixe.consts.get? a = some { buf := Ixon.ser c, len := (Ixon.ser c).size }) : recordAt ixe a = some c := by
  unfold recordAt
  rw [h]
  exact (StoredEncoding.get?_serConstant wire).1

/-- **A claimed record's block is stored and is its own block.** -/
theorem claim_block (bw : BlocksWire) {ixe : Ixon.Env} {n : Ix.Name} {a : Address} (h : ClaimedAt ixe n a) :
    ∃ c, recordAt ixe (blockAt ixe a) = some c ∧ ownerOf (blockAt ixe a) c = blockAt ixe a := by
  obtain ⟨cenv, A, k, r, c, b, hr, hclaim, ha, hb⟩ := h
  have shape := runBlock_shape hr
  have wire := bw _ _ _ _ _ hr
  have blockRec : recordAt ixe r.blockAddr = some r.block := by
    rw [shape.bytes] at hb
    exact recordAt_ser wire hb
  -- the block's own record
  have atBlock : ∃ c, recordAt ixe (blockAt ixe r.blockAddr) = some c ∧
      ownerOf (blockAt ixe r.blockAddr) c = blockAt ixe r.blockAddr := by
    have hat : blockAt ixe r.blockAddr = r.blockAddr := by
      unfold blockAt
      rw [blockRec]
      exact shape.built.owner _
    rw [hat]
    exact ⟨r.block, blockRec, shape.built.owner _⟩
  unfold Resolution.claimWrites at hclaim
  split at hclaim
  · simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, rfl⟩ := hclaim
    exact atBlock
  · obtain ⟨p, hp, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rcases shape.rows p hp with same | ⟨pwire, powner⟩
    · rw [same, ← shape.bytes, ← shape.addr]
      exact atBlock
    · have prec := recordAt_ser pwire ha
      have hat : blockAt ixe (Address.admissionHash (Ixon.ser p.2.1)) = r.blockAddr := by
        unfold blockAt
        rw [prec]
        exact powner _
      rw [hat]
      exact ⟨r.block, blockRec, shape.built.owner _⟩

/-- **`Layout.block` from the fold's claims**, given that the canonical sharing builds constants
in the wire domain (`BlocksWire`). -/
theorem layoutBlock_of_claimed (bw : BlocksWire) {ixe : Ixon.Env} {g : Ix.LeanIngress.Graph}
    (claimed : ∀ (i : Nat) (gr : Ix.LeanIngress.Group), g.groups[i]? = some gr → ∀ n ∈ gr.names, ∀ a,
      addrOf ixe n = some a → ClaimedAt ixe n a) :
    ∀ (i : Nat) (gr : Ix.LeanIngress.Group), g.groups[i]? = some gr → ∀ n ∈ gr.names, ∀ a,
      addrOf ixe n = some a →
        ∃ c, recordAt ixe (blockAt ixe a) = some c ∧ ownerOf (blockAt ixe a) c = blockAt ixe a :=
  fun i gr hgr n hn a ha => claim_block bw (claimed i gr hgr n hn a ha)

/--
info: 'Ix.Cert.BlockLayout.layoutBlock_of_claimed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms layoutBlock_of_claimed

end Ix.Cert.BlockLayout
