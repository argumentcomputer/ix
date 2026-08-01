import Ix.Tc.Verify.Env
import Ix.Tc.Verify.Monad
import Ix.Tc.Verify.InstUniv
import Ix.Tc.Verify.Cache
import Ix.Tc.Verify.EquivalenceManager

/-!
# The verification world and the run invariant

`TcStateWF` is the concrete/ghost boundary used by the Hoare proofs.  It
deliberately separates three independent facts:

* `TrustedCatalogRel` justifies exactly the declarations already admitted to
  the Theory environment;
* `LoadedAgrees` says every lazily loaded concrete declaration is the entry
  committed by the immutable catalog, without typing that entry;
* `InternTable.WF` gives structural coherence for hash-consing.

Consequently, a concrete `KEnv` may contain a pending or ill-typed catalog
entry while `TcStateWF` still holds.  Loading a catalog entry leaves the
world unchanged.  Growing the trusted world is a separate ghost operation
whose API requires the new `VDecl.WF` evidence.

`TcInv world₀ s` existentially hides the current world while retaining a
monotone extension proof from the caller's baseline.  Fixed-world Hoare
triples are proved first below; their error branches retain exactly the same
world, so ordinary state mutation cannot silently promote a declaration.

Ambient-inductive admission is carried by the trusted log beginning in G2a.
G4 layers finite-support cache provenance onto this deliberately small core
through `KernelStateWF` below. Dual-context agreement and the concrete
reduction/inference/native semantic contracts remain K1/K2 obligations.
-/

namespace Ix.Tc

open Lean4Lean (VDecl VExpr)

/-- A concrete checker state is coherent with one verification world.

The trusted catalog log is semantic; loaded agreement is representation-only.
In particular, neither `loaded` nor `intern` implies that an untrusted catalog
entry is well-typed. -/
structure TcStateWF (trProj : RawProjRel) (s : TcState .anon)
    (world : VerifyWorld) : Prop where
  trustedCatalog : TrustedCatalogRel trProj world
  loaded : LoadedAgrees world.catalog s.env
  intern : s.env.intern.WF

/-- The wide frame used by intern-table walkers: preserving the loaded
constant map and re-establishing intern coherence preserves `TcStateWF`.
Fuel, flags, scratch state, and statistics remain unconstrained. -/
theorem TcStateWF.of_consts_eq {trProj : RawProjRel}
    {s s' : TcState .anon} {world : VerifyWorld}
    (h : TcStateWF trProj s world)
    (hc : s'.env.consts = s.env.consts)
    (hi : s'.env.intern.WF) :
    TcStateWF trProj s' world := by
  refine ⟨h.trustedCatalog, ?_, hi⟩
  intro id c hget
  apply h.loaded
  simpa [KEnv.get?, hc] using hget

/-- `of_consts_eq` when the entire concrete environment is untouched. -/
theorem TcStateWF.of_env_eq {trProj : RawProjRel}
    {s s' : TcState .anon} {world : VerifyWorld}
    (h : TcStateWF trProj s world) (he : s'.env = s.env) :
    TcStateWF trProj s' world :=
  h.of_consts_eq (by rw [he]) (he ▸ h.intern)

/-- Lazy ingress is representation-only.  Loading the catalog's exact entry
does not change the trusted set or the Theory environment. -/
theorem TcStateWF.load {trProj : RawProjRel} {s : TcState .anon}
    {world : VerifyWorld} {id : KId .anon} {c : KConst .anon}
    (h : TcStateWF trProj s world) (hcat : world.catalog id = some c) :
    TcStateWF trProj
      { s with env := s.env.insert id c }
      world := by
  exact ⟨h.trustedCatalog, LoadedAgrees.insert h.loaded hcat, h.intern⟩

/-- Semantic admission is ghost-only and requires the declaration-WF fact
supplied by successful checking.  The concrete state remains unchanged. -/
theorem TcStateWF.promote {trProj : RawProjRel} {s : TcState .anon}
    {world : VerifyWorld} {id : KId .anon} {d : VDecl}
    {venv' : Lean4Lean.VEnv}
    (h : TcStateWF trProj s world)
    (hpending : PendingDecl trProj world id d)
    (hwf : VDecl.WF world.venv d venv') :
    ∃ world',
      Promotes world (fun target => target = id) world' ∧
      TcStateWF trProj s world' ∧
      TrustedDecl trProj world' id d := by
  obtain ⟨world', hpromotes, htrustedCatalog, htrustedDecl⟩ :=
    TrustedCatalogRel.promote h.trustedCatalog hpending hwf
  refine ⟨world', hpromotes, ?_, htrustedDecl⟩
  exact ⟨htrustedCatalog,
    (LoadedAgrees.world_iff hpromotes.1).mp h.loaded,
    h.intern⟩

/-- The run invariant: some world extending the caller's baseline describes
the current concrete state. -/
def TcInv (trProj : RawProjRel) (world₀ : VerifyWorld)
    (s : TcState .anon) : Prop :=
  ∃ world, world₀ ≤ world ∧ TcStateWF trProj s world

/-! ## G4 semantic-cache layer -/

/-- The complete stable checker invariant at a finite run boundary.

`TcStateWF` remains the small catalog/trusted/intern core used by individual
walker proofs. This layer adds the exact run support and semantic provenance
for every warm cache entry. The authority is stable: no pending declaration
or active block is available to justify a cache dependency. Internal block
proofs use `CacheAuthority` directly while the block is active, then establish
this stable form only after promotion or error rollback. -/
structure KernelStateWF (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (s : TcState .anon) : Prop where
  core : TcStateWF trProj s world
  internSupport : support.CoversIntern s.env.intern
  caches : CacheInvariant semantics (CacheAuthority.stable world) support s.env
  equivalences : EquivManager.WF
    (semantics.Equiv (CacheAuthority.stable world) support) s.equivManager

/-- Existential current-world form of the complete G4 state invariant. -/
def KernelTcInv (semantics : CacheSemantics) (trProj : RawProjRel)
    (world₀ : VerifyWorld) (support : RunSupport)
    (s : TcState .anon) : Prop :=
  ∃ world, world₀ ≤ world ∧ KernelStateWF semantics trProj world support s

namespace KernelStateWF

/-- Rebase a stable kernel invariant after ghost-only world growth.  The
caller supplies the core relation for the larger world (normally produced by
`TcStateWF.promote`); cache and equivalence-manager facts transport
monotonically along the same world extension. -/
theorem rebaseWorld {semantics : CacheSemantics}
    {trProj : RawProjRel} {beforeWorld afterWorld : VerifyWorld}
    {support : RunSupport} {s : TcState .anon}
    (hle : beforeWorld ≤ afterWorld)
    (hcore : TcStateWF trProj s afterWorld)
    (h : KernelStateWF semantics trProj beforeWorld support s) :
    KernelStateWF semantics trProj afterWorld support s := by
  have hauth : CacheAuthority.stable beforeWorld ≤
      CacheAuthority.stable afterWorld :=
    CacheAuthority.stable_mono hle
  exact
    { core := hcore
      internSupport := h.internSupport
      caches := h.caches.mono hauth
      equivalences := h.equivalences.mono
        (fun hrel => semantics.equivMono hauth hrel) }

/-- Build the complete state invariant when the physical environment has no
semantic cache entries. Constants, blocks, and intern tables may be nonempty. -/
theorem of_no_cache_entries {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {s : TcState .anon} (hcore : TcStateWF trProj s world)
    (hintern : support.CoversIntern s.env.intern)
    (hequiv : s.equivManager = EquivManager.empty)
    (hempty : ∀ entry, ¬s.env.HasCacheEntry entry) :
    KernelStateWF semantics trProj world support s :=
  ⟨hcore, hintern, CacheInvariant.of_no_entries hempty, by
    rw [hequiv]
    exact EquivManager.WF.empty⟩

/-- A physical hit in a stable state exposes its complete provenance. -/
theorem cacheHit {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {s : TcState .anon}
    (h : KernelStateWF semantics trProj world support s)
    {entry : CacheEntry} (hhit : s.env.HasCacheEntry entry) :
    CacheProvenance semantics (CacheAuthority.stable world) support entry :=
  h.caches.hit hhit

/-- No warm cache hit at a stable boundary—reduction or structural—can name
the pending declaration as a dependency. -/
theorem pendingCacheIsolation {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {s : TcState .anon} (h : KernelStateWF semantics trProj world support s)
    {target : KId .anon} {d : VDecl}
    (hpending : PendingDecl trProj world target d)
    {entry : CacheEntry} (hhit : s.env.HasCacheEntry entry) :
    ¬entry.References support target := by
  apply (h.cacheHit hhit).pending_isolation_stable
  · exact fun _ hactive => hactive
  · exact hpending

/-- Reassemble the complete stable invariant after the public check-error
boundary. The failed run may retain lazy loads and intern growth, so those
ordinary core/support facts come from `after`; every semantic cache fact comes
from the already-valid `before` state, except unconditional cached errors. -/
theorem restoreCheckCachesOnError {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {before after : TcState .anon}
    (hbefore : KernelStateWF semantics trProj world support before)
    (hafterCore : TcStateWF trProj after world)
    (hafterIntern : support.CoversIntern after.env.intern) :
    KernelStateWF semantics trProj world support
      (before.restoreCheckCachesOnError after) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hafterCore.of_consts_eq
    · simp [TcState.restoreCheckCachesOnError]
    · simpa [TcState.restoreCheckCachesOnError] using hafterCore.intern
  · simpa [TcState.restoreCheckCachesOnError] using hafterIntern
  · exact hbefore.caches.restoreCheckCachesOnError
  · simpa [TcState.restoreCheckCachesOnError] using hbefore.equivalences

end KernelStateWF

namespace KernelTcInv

/-- A fixed-world complete invariant embeds into its existential baseline
form. -/
theorem of_state {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {s : TcState .anon}
    (h : KernelStateWF semantics trProj world support s) :
    KernelTcInv semantics trProj world support s :=
  ⟨world, VerifyWorld.LE.rfl, h⟩

end KernelTcInv

theorem TcStateWF.tcInv {trProj : RawProjRel} {s : TcState .anon}
    {world : VerifyWorld} (h : TcStateWF trProj s world) :
    TcInv trProj world s :=
  ⟨world, VerifyWorld.LE.rfl, h⟩

/-- Weaken the baseline world. -/
theorem TcInv.mono {trProj : RawProjRel}
    {world₀ world₀' : VerifyWorld} {s : TcState .anon}
    (hle : world₀' ≤ world₀) (h : TcInv trProj world₀ s) :
    TcInv trProj world₀' s :=
  let ⟨world, hworld, hwf⟩ := h
  ⟨world, hle.trans hworld, hwf⟩

/-- Every invariant witness carries an explicitly justified, well-formed
Theory environment. -/
theorem TcInv.venv_wf {trProj : RawProjRel} {world₀ : VerifyWorld}
    {s : TcState .anon} (h : TcInv trProj world₀ s) :
    ∃ world, world₀ ≤ world ∧ world.venv.WF :=
  let ⟨world, hworld, hwf⟩ := h
  ⟨world, hworld, hwf.trustedCatalog.wf⟩

/-- A concrete lookup is only a catalog lookup.  Semantic lookup additionally
requires that the id is trusted in this exact world. -/
theorem TcStateWF.find? {trProj : RawProjRel} {s : TcState .anon}
    {world : VerifyWorld} (h : TcStateWF trProj s world)
    {id : KId .anon} {c : KConst .anon}
    (hget : s.env.get? id = some c) (htrusted : world.trusted id) :
    world.catalog id = some c ∧
      TrustedCatalogEntry trProj world.catalog world.nameOf world.venv id :=
  ⟨h.loaded hget, h.trustedCatalog.find htrusted⟩

/-- Consumer-facing trusted resolution.  A concrete cache hit plus trust
yields exact unified provenance without a whole-`KEnv` translation premise. -/
theorem TcStateWF.resolve {trProj : RawProjRel} {s : TcState .anon}
    {world : VerifyWorld} (h : TcStateWF trProj s world)
    {id : KId .anon} {c : KConst .anon}
    (hget : s.env.get? id = some c) (htrusted : world.trusted id) :
    ∃ name ci, TrustedConstRel trProj world id c name ci :=
  h.trustedCatalog.resolve htrusted (h.loaded hget)

/-- Trusted lookup lifted through the existential current-world witness.
Trust in the baseline is enough because world extension never forgets it. -/
theorem TcInv.find? {trProj : RawProjRel} {world₀ : VerifyWorld}
    {s : TcState .anon} (h : TcInv trProj world₀ s)
    {id : KId .anon} {c : KConst .anon}
    (hget : s.env.get? id = some c) (htrusted : world₀.trusted id) :
    ∃ world, world₀ ≤ world ∧
      world.catalog id = some c ∧
      TrustedCatalogEntry trProj world.catalog world.nameOf world.venv id := by
  obtain ⟨world, hworld, hwf⟩ := h
  obtain ⟨hcat, hlookup⟩ := hwf.find? hget (hworld.trusted htrusted)
  exact ⟨world, hworld, hcat, hlookup⟩

/-- Unified trusted resolution lifted through the existential current world. -/
theorem TcInv.resolve {trProj : RawProjRel} {world₀ : VerifyWorld}
    {s : TcState .anon} (h : TcInv trProj world₀ s)
    {id : KId .anon} {c : KConst .anon}
    (hget : s.env.get? id = some c) (htrusted : world₀.trusted id) :
    ∃ world, world₀ ≤ world ∧
      ∃ name ci, TrustedConstRel trProj world id c name ci := by
  obtain ⟨world, hworld, hwf⟩ := h
  exact ⟨world, hworld, hwf.resolve hget (hworld.trusted htrusted)⟩

/-! ## Adversarial state fixture -/

namespace IllTypedPending

/-- The pending declaration is concretely loaded, but remains outside the
trusted semantic world. -/
def loadedEnv : KEnv .anon :=
  ({} : KEnv .anon).insert targetId concrete

def state (prims : Primitives .anon) : TcState .anon :=
  { env := loadedEnv, prims, ctxId := fixtureAddress }

theorem stateWF (prims : Primitives .anon) :
    TcStateWF RawProjRel.none (state prims) world := by
  refine ⟨trustedCatalogRel, ?_, ?_⟩
  · change LoadedAgrees world.catalog loadedEnv
    exact loaded_pending_but_not_wf.1
  · exact InternTable.WF.empty

/-- G1's central adversarial witness: the complete state invariant and
pending precondition are inhabited even though declaration WF is impossible.
This rules out a hidden whole-`KEnv` typing premise in `TcInv`. -/
theorem tcInv_pending_but_not_wf (prims : Primitives .anon) :
    TcInv RawProjRel.none world (state prims) ∧
      PendingDecl RawProjRel.none world targetId theoryDecl ∧
      ¬∃ env', VDecl.WF world.venv theoryDecl env' :=
  ⟨(stateWF prims).tcInv, pending, theoryDecl_not_wf⟩

end IllTypedPending

/-! ## Validation on stateful helpers -/

/-- `tick` preserves an exact world on both success and error.  This is the
fixed-world form of the no-promotion-on-error guarantee. -/
theorem TcM.tick.tcStateWF {trProj : RawProjRel} {world : VerifyWorld}
    {s : TcState .anon} :
    TcM.WF (fun s => TcStateWF trProj s world) s
      (TcM.tick (m := .anon))
      (fun _ s' => s'.recFuel = s.recFuel - 1)
      (fun e s' => e = .maxRecFuel ∧ s' = s) :=
  TcM.tick.wf fun _ h => h.of_env_eq rfl

/-- Existential-world wrapper for callers threading a baseline world. -/
theorem TcM.tick.tcInv {trProj : RawProjRel} {world₀ : VerifyWorld}
    {s : TcState .anon} :
    TcM.WF (TcInv trProj world₀) s (TcM.tick (m := .anon))
      (fun _ s' => s'.recFuel = s.recFuel - 1)
      (fun e s' => e = .maxRecFuel ∧ s' = s) :=
  TcM.tick.wf fun _ h =>
    let ⟨world, hworld, hwf⟩ := h
    ⟨world, hworld, hwf.of_env_eq rfl⟩

/-- `instantiateUnivParams` preserves one exact world on both outcomes; only
the structurally coherent intern table changes. -/
theorem TcM.instantiateUnivParams.tcStateWF
    {trProj : RawProjRel} {world : VerifyWorld}
    {S : KExpr .anon → Prop} {us : Array (KUniv .anon)}
    {e : KExpr .anon} {s : TcState .anon}
    (hcf : KExpr.CollisionFree S)
    (hreach : ∀ x, KExpr.InstUnivReach us e x → S x)
    (hsup : ∀ x, s.env.intern.ExprSupport x → S x) :
    TcM.WF (fun s => TcStateWF trProj s world) s
      (TcM.instantiateUnivParams e us)
      (fun r s' => KExpr.instantiateUnivParamsSpec e us = .ok r ∧
        s' = { s with env := { s.env with intern := s'.env.intern } })
      (fun _ s' =>
        s' = { s with env := { s.env with intern := s'.env.intern } }) := by
  intro hwf
  have hrunWF := TcM.instantiateUnivParams_wf hcf hreach
    (s := s) ⟨hwf.intern, hsup⟩
  match hrun : TcM.instantiateUnivParams e us s with
  | .ok r s' =>
    rw [hrun] at hrunWF
    have hintern := hrunWF.1.1
    have hspec := hrunWF.2.1
    have hframe := hrunWF.2.2.1
    have hc : s'.env.consts = s.env.consts :=
      congrArg (fun t => t.env.consts) hframe
    exact ⟨hwf.of_consts_eq hc hintern, hspec, hframe⟩
  | .error err s' =>
    rw [hrun] at hrunWF
    have hintern := hrunWF.1.1
    have hframe := hrunWF.2.1
    have hc : s'.env.consts = s.env.consts :=
      congrArg (fun t => t.env.consts) hframe
    exact ⟨hwf.of_consts_eq hc hintern, hframe⟩

/-- Existential-world wrapper for the run invariant. -/
theorem TcM.instantiateUnivParams.tcInv
    {trProj : RawProjRel} {world₀ : VerifyWorld}
    {S : KExpr .anon → Prop} {us : Array (KUniv .anon)}
    {e : KExpr .anon} {s : TcState .anon}
    (hcf : KExpr.CollisionFree S)
    (hreach : ∀ x, KExpr.InstUnivReach us e x → S x)
    (hsup : ∀ x, s.env.intern.ExprSupport x → S x) :
    TcM.WF (TcInv trProj world₀) s
      (TcM.instantiateUnivParams e us)
      (fun r s' => KExpr.instantiateUnivParamsSpec e us = .ok r ∧
        s' = { s with env := { s.env with intern := s'.env.intern } })
      (fun _ s' =>
        s' = { s with env := { s.env with intern := s'.env.intern } }) := by
  intro hI
  obtain ⟨world, hworld, hwf⟩ := hI
  have hrunWF := TcM.instantiateUnivParams.tcStateWF
    (trProj := trProj) (world := world) hcf hreach hsup hwf
  match hrun : TcM.instantiateUnivParams e us s with
  | .ok r s' =>
    rw [hrun] at hrunWF
    exact ⟨⟨world, hworld, hrunWF.1⟩, hrunWF.2⟩
  | .error err s' =>
    rw [hrun] at hrunWF
    exact ⟨⟨world, hworld, hrunWF.1⟩, hrunWF.2⟩

end Ix.Tc
