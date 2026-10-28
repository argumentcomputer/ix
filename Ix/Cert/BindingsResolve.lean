import Ix.Cert.ClosureResolve
import Ix.Cert.RunOwnership

/-! # Every binding of a fold state resolves in the artifact

`BlockContext.BoundResolve ixe cenv`: every address the snapshot `cenv` binds holds a stored
record of the artifact that resolves there. It is the fold premise of every segment reading's
compile-side context (`SingletonReads.external`).

The constructor positions a resolving constructor projection needs are not the compile's own
fact for a name outside the closure (the compiler copies a constructor's declared index into its
block and addresses the constructor by its position), so they are the named premise
`ConstructorIndices env`, the meaning of the compile report's constructor index check
(`constructorIndices`). With it:
* every binding of a state the fold reaches holds a record of the state's store that resolves
  in that store (`reach_boundOK`): a step keeps the old bindings (stores only grow, and a record
  resolves alike in a larger store), and a new binding is a primary claim of a checked merge,
  whose block record the merge stores (`applyCompiled_stored`), and which resolves
  (`ClosureResolve.runBlock_claims`);
* a state of the fold's run stores records the artifact stores (`onRun_persists`, then the
  assembly), so its bindings resolve in the artifact (`boundResolve_onRun`).

`claimedIn_bound` is `LayoutExtra.claimedIn_of` with `BoundResolve` at the claim's snapshot. -/

namespace Ix.Cert.BindingsResolve

open Ix.Kernel.Reader (Store resolveSource)
open Ix.CompileM Ix.CompileCert Ix.Cert.Resolution Ix.Cert.Schedule
open Ix.Compile.ExactKey (ExactName)
open Ix.Cert.BlockContext (BoundResolve)
open Ix.Cert.ClosureResolve (PositionsIn ClaimsResolve)

theorem forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ j (hj : j < m.length), ∃ hl : j < l.length, R l[j] m[j]
  | _, _, .nil, _, hj => absurd hj (Nat.not_lt_zero _)
  | _, _, .cons h _, 0, _ => ⟨Nat.zero_lt_succ _, h⟩
  | _, _, .cons _ t, j + 1, hj => by
    obtain ⟨hl, r⟩ := forall₂_get t j (Nat.lt_of_succ_lt_succ hj)
    exact ⟨Nat.succ_lt_succ hl, r⟩

/-- An environment that reads the input's constants lists every block's constructors at their
positions. -/
theorem positionsIn_of {env : Ix.Environment} (idx : ConstructorIndices env) {E : Ix.Environment}
    (hE : ∀ x, E.get? x = env.consts.get? x) (all : Ix.Set Ix.Name) : PositionsIn E all := by
  intro n _ val hval cs looked j hj
  rw [hE] at hval
  obtain ⟨hl, hc⟩ := forall₂_get looked j hj
  rw [hE] at hc
  simp only [Array.length_toList] at hl
  exact idx n val hval j hl _ (by simpa using hc)

/-! ## A fold state's bindings resolve in its store -/

/-- A store of record bytes, decoded record by record. -/
def storeOf (m : Std.HashMap Address ByteArray) : Store :=
  fun a => (m.get? a).bind fun b => ({ buf := b, len := b.size } : Ixon.LazyConstant).get?

theorem storeOf_mono {m m' : Std.HashMap Address ByteArray}
    (h : ∀ a b, m.get? a = some b → m'.get? a = some b) :
    ∀ a c, storeOf m a = some c → storeOf m' a = some c := by
  intro a c hc
  unfold storeOf at hc ⊢
  cases hm : m.get? a with
  | none => rw [hm] at hc; cases hc
  | some b => rw [hm] at hc; rw [h a b hm]; exact hc

theorem storeOf_ser {m : Std.HashMap Address ByteArray} {a : Address} {c : Ixon.Constant} (wire : c.wireWF)
    (fits : Ixon.Bounded.univNodes c.univs ≤ Ixon.loadMaxUnivNodes)
    (h : m.get? a = some (Ixon.ser c)) : storeOf m a = some c := by
  unfold storeOf
  rw [h]
  exact (StoredEncoding.get?_serConstant wire fits).1

/-- **Every binding of a state holds a record of its store that resolves there.** -/
def BoundOK (c : CompileEnv) : Prop :=
  ∀ (n : ExactName) (a : Address), c.nameToAddr.get? n = some a →
    ∃ rc, storeOf c.constants a = some rc ∧ (resolveSource (storeOf c.constants) a rc).isSome = true

/-- **A primary claim of a block resolves** in every store holding the block: its record is the
block or one of its projections, wire-valid, and `ClaimsResolve`. -/
theorem claim_resolves {cenv : CompileEnv} {all : Ix.Set Ix.Name} {lo : Ix.Name} {r : BlockResult}
    {cache : BlockState} (hr : runBlock cenv all lo = .ok (r, cache)) (pos : PositionsIn cenv.env all)
    {store : Store} (hblock : store r.blockAddr = some r.block) {n : Ix.Name} {a : Address} {b : ByteArray}
    (hclaim : (n, a, b) ∈ claimWrites lo r) :
    ∃ rc, rc.wireWF ∧ Ixon.Bounded.univNodes rc.univs ≤ Ixon.loadMaxUnivNodes ∧
      b = Ixon.ser rc ∧ (resolveSource store a rc).isSome = true := by
  have wire := BlockWire.blocksWire _ _ _ _ _ hr
  have shape := BlockLayout.runBlock_shape hr
  have fits := BlockRecords.runBlock_bounded hr
  have claims := ClosureResolve.runBlock_claims hr pos
  unfold claimWrites at hclaim
  split at hclaim
  · rename_i hempty
    simp only [List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hclaim
    obtain ⟨-, rfl, rfl⟩ := hclaim
    exact ⟨r.block, wire, fits.1, shape.bytes, ClosureResolve.lone_resolves (claims.1 hempty) _ _⟩
  · obtain ⟨p, hp, e⟩ := Array.mem_map.mp hclaim
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    have pwire : p.2.1.wireWF := by
      rcases shape.rows p hp with same | ⟨pw, -, -⟩
      · rw [same]; exact wire
      · exact pw
    exact ⟨p.2.1, pwire, fits.2 p hp, rfl, claims.2 p hp store hblock⟩

/-- **A step keeps every binding resolving**: old bindings in a larger store, and a new binding
is a claim of the checked merge, which stores the claiming block's record. -/
theorem boundOK_step {snap acc : DriverAcc} {lo : Ix.Name} {all : Ix.Set Ix.Name}
    (pos : PositionsIn snap.cenv.env all) (h : BoundOK acc.cenv) :
    BoundOK (applyAuxBlockOutcome acc lo all (auxBlockOutcome snap.cenv lo all)).1.cenv := by
  generalize ho : auxBlockOutcome snap.cenv lo all = o
  have st := applyAuxBlockOutcome_step acc lo all o
  have grow := storeOf_mono st.1.1
  have old : ∀ (n : ExactName) (a : Address), acc.cenv.nameToAddr.get? n = some a →
      ∃ rc, storeOf (applyAuxBlockOutcome acc lo all o).1.cenv.constants a = some rc ∧
        (resolveSource (storeOf (applyAuxBlockOutcome acc lo all o).1.cenv.constants) a rc).isSome = true := by
    intro n a hn
    obtain ⟨rc, hrc, hres⟩ := h n a hn
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hres
    refine ⟨rc, grow a rc hrc, ?_⟩
    rw [BlockContext.resolveSource_of_owner hq fun cb hcb => grow _ cb hcb]
    rfl
  intro n a hn
  rcases st.2 n a hn with hold | ⟨b, hclaim, hb⟩
  · exact old n a hold
  · cases o with
    | failed msg => exact hclaim.elim
    | compiled r cs =>
      have hr := auxBlockOutcome_compiled ho
      by_cases hc : checkCompiledBlock acc.cenv lo r cs = .ok ()
      · have stored := FreshSnapshot.applyCompiled_stored acc lo all r cs hc
        have shape := BlockLayout.runBlock_shape hr
        have blockRec : storeOf (applyAuxBlockOutcome acc lo all (.compiled r cs)).1.cenv.constants r.blockAddr =
            some r.block := by
          rw [shape.bytes] at stored
          exact storeOf_ser (BlockWire.blocksWire _ _ _ _ _ hr)
            (BlockRecords.runBlock_bounded hr).1 stored
        obtain ⟨rc, wire, fits, hbytes, hres⟩ := claim_resolves hr pos blockRec hclaim
        rw [hbytes] at hb
        exact ⟨rc, storeOf_ser wire fits hb, hres⟩
      · have same := FreshSnapshot.applyCompiled_failed acc lo all r cs hc
        rw [same] at hn
        exact old n a hn

/-- **Every state the fold reaches from a start with no binding keeps its bindings resolving**,
when the start reads the input's constants and the input's inductives list their constructors at
their positions. -/
theorem reach_boundOK {env : Ix.Environment} (idx : ConstructorIndices env) {blocks : Ix.CondensedBlocks}
    {init : DriverAcc} (empty : init.cenv.nameToAddr = {})
    (reads : ∀ x, init.cenv.env.get? x = env.consts.get? x) {acc : DriverAcc} (h : Reach blocks init acc) :
    BoundOK acc.cenv := by
  induction h with
  | init =>
    intro n a hn
    rw [empty, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at hn
    cases hn
  | @step snap acc rep all hsnap _ _ _ _ ih =>
    refine boundOK_step (positionsIn_of idx (fun x => ?_) all) ih
    rw [reach_env hsnap]
    exact reads x

/-! ## In the artifact -/

/-- The records the compile's final environment stores are the artifact's. -/
theorem final_stored {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures} {cenv : CompileEnv}
    (hu : compileUnchecked env = .ok (ixe, failures, cenv)) :
    ∀ a b, cenv.constants.get? a = some b → ixe.consts.get? a = some { buf := b, len := b.size } := by
  obtain ⟨bytes, hf⟩ := compileUnchecked_fold hu
  obtain ⟨-, -, st, -, -, -, finalized, -, hconsts, -, -⟩ := FreshSnapshot.compileEnvFold_final_blobs hf
  intro a b hb
  rw [← finalized]
  exact assembleEnv_consts _ (by rw [← hconsts]; exact hb)

/-- **Every binding of a state of the fold's run resolves in the artifact** (`BoundResolve`),
when the input's inductives list their constructors at their positions. -/
theorem boundResolve_onRun {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    {cenv cenv₀ : CompileEnv} {blocks : Ix.CondensedBlocks} {sched : FoldSchedule}
    (hu : compileUnchecked env = .ok (ixe, failures, cenv)) (idx : ConstructorIndices env)
    (hrun : FoldRun { consts := env.consts } blocks cenv cenv₀ sched) {acc : DriverAcc}
    (hacc : OnRun blocks sched (FoldState.init cenv₀ blocks sched) acc) : BoundResolve ixe acc.cenv := by
  obtain ⟨st, h₀, henv, hst, -, hkept, -⟩ := hrun
  have ok := reach_boundOK idx (blocks := blocks) (init := (FoldState.init cenv₀ blocks sched).acc)
    ((init_nameToAddr _ _ _).trans h₀)
    (fun x => by rw [henv, ClosureClaims.view_get, ClosureClaims.input_get]) (onRun_reach hacc)
  have persists := RunOwnership.onRun_persists StepKeeps.stepKeeps hst hacc
  have inArtifact : ∀ a c, storeOf acc.cenv.constants a = some c → recordAt ixe a = some c := by
    intro a c hc
    unfold storeOf at hc
    cases hb : acc.cenv.constants.get? a with
    | none => rw [hb] at hc; cases hc
    | some b =>
      rw [hb] at hc
      unfold recordAt
      rw [final_stored hu a b (hkept a b (persists.consts a b hb))]
      exact hc
  intro m a hb
  have hnone : (ExpressionState.bindingView ({} : BlockState)).get? m = none :=
    Std.HashMap.get?_eq_getElem?.trans Std.HashMap.getElem?_empty
  unfold ExpressionState.lookupBinding at hb
  rw [hnone] at hb
  obtain ⟨rc, hrc, hres⟩ := ok m a hb
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hres
  refine ⟨rc, inArtifact a rc hrc, ?_⟩
  rw [BlockContext.resolveSource_of_owner hq fun cb hcb => inArtifact _ cb hcb]
  rfl

/-- **`LayoutExtra.claimedIn_of` with the claim's snapshot's bindings resolving**: a closure name's
published record is a primary claim of its block's compile, and every binding of the compile's
environment resolves in the artifact. -/
theorem claimedIn_bound {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (P : Premises env roots sub ixe failures t envQ) (idx : ConstructorIndices env) :
    ∀ m ci, (m, ci) ∈ sub.consts.toList → ∀ a, ClosureLayout.addrOf ixe m = some a →
      ∃ (cenv : CompileEnv) (A : Ix.Set Ix.Name) (k : Ix.Name) (r : BlockResult) (c : BlockState)
        (b : ByteArray),
        (∀ x, cenv.env.get? x = env.consts.get? x) ∧ A.contains k = true ∧ LayoutExtra.MembersIn sub A ∧
        runBlock cenv A k = .ok (r, c) ∧ (m, a, b) ∈ Resolution.claimWrites k r ∧
        ixe.consts.get? a = some { buf := b, len := b.size } ∧
        ixe.consts.get? r.blockAddr = some { buf := r.blockBytes, len := r.blockBytes.size } ∧
        BoundResolve ixe cenv := by
  intro m ci hci a ha
  have hcl : IsClosure env roots sub := P.source.1
  obtain ⟨cenv, blocks, cenv₀, sched, hu, hblocks, hrun, -, owned⟩ :=
    Ix.Cert.compileReport_owned_block P.compiled hcl P.none
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published P hci
  have haddr : a = named.addr := by
    unfold ClosureLayout.addrOf at ha
    rw [hget] at ha
    exact (Option.some.inj ha).symm
  subst haddr
  have hin : env.consts.contains m = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
      SourceStoredNames.stored_get (SourceStoredNames.stored_input P hci)]
    rfl
  have hn := LayoutExtra.published_resolved P.compiled hu hmem hget hin
  have hs : (sub.consts.get? m).isSome = true := by
    rw [SourceStoredNames.stored_get hci]
    rfl
  obtain ⟨-, snap, rep, all, r, c, b, hsnap, hall, -, hsub, hr, hclaim, hb, -, -, hblock, -⟩ :=
    owned m named.addr hn hs
  have bound := boundResolve_onRun hu idx hrun hsnap
  obtain ⟨-, -, henv, -⟩ := hrun
  have hE : ∀ x, snap.cenv.env.get? x = env.consts.get? x := fun x => by
    rw [reach_env (onRun_reach hsnap), henv, ClosureClaims.view_get, ClosureClaims.input_get]
  subst hblocks
  exact ⟨snap.cenv, all, blockKey rep all, r, c, b, hE, blockKey_mem (Condense.condense_nonempty hall),
    hsub, hr, hclaim, hb, hblock, bound⟩

/--
info: 'Ix.Cert.BindingsResolve.boundResolve_onRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms boundResolve_onRun

/--
info: 'Ix.Cert.BindingsResolve.claimedIn_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms claimedIn_bound

end Ix.Cert.BindingsResolve
