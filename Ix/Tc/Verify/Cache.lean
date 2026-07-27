import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.Env
import Ix.Tc.Verify.Monad
import Ix.Tc.Verify.Support
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
# Cache provenance and pending-declaration isolation

This is the G4 boundary between an optimization hit and a semantic fact.
`KEnv` stores only compact address keys, values, and booleans; it does not
store the world or expression witnesses under which an entry was produced.
The verification therefore carries that missing data as ghost provenance:

* `CacheEntry` is an exhaustive tagged view of the 18 semantic cache fields
  in `KEnv` (seven expression-result maps, two defeq maps, three negative/
  stuck sets, unfold, is-prop, and four inductive/block families plus block
  results);
* `CacheAuthority` separates already-trusted declarations from an active
  atomic block. Reduction/inference entries never receive active-block
  authority; only the explicitly structural block cache kinds do;
* `CacheEntry.SupportedBy` ties every address key and cached expression value
  to the same finite `RunSupport` used by the collision-freedom hypotheses;
* `CacheEntry.ReferencesAuthorized` records that every direct constant root
  behind an entry is trusted (or, for a structural block artifact only, is an
  active block member); and
* `CacheSemantics.Valid` is the exact family of C1/K1/K2 semantic meanings.
  G4 keeps it parametric and requires its world monotonicity. A run chooses
  its final finite support up front; K1 and K2 instantiate and preserve the
  contract at each concrete insertion site.

The split is deliberate. This file proves generic cache-hit, world-extension,
support-witness weakening, reset, clearing, error-restoration, and
pending-isolation laws without pretending the still-partial
whnf/infer/defeq implementations have already been verified.

## Constant-lookup audit

Every `checkConst`-reachable concrete lookup is one of these roles:

1. `subject`: the initial target/member read in `Check.lean`;
2. `blockPeer`: classification and inductive/recursor coordination reads;
3. `semantic`: expression inference, delta unfolding, proof irrelevance,
   projection/iota reduction, native-definition unfolding, and safety walks.

Only role (1) may read a standalone pending target. Role (2) is confined to
the active atomic block. Every reduction/delta/cache fact is role (3), so a
pending target cannot justify its own type or value.

These roles are proof-side labels: the production `TcM.getConst` API is not
yet intrinsically capability-tagged. G4 proves the standalone raw-translation
barrier and the stable-cache barrier. K1/K2 must still classify and discharge
`LookupScope.Allows` at each whnf/infer/defeq/inductive call site; this audit
does not treat an untagged concrete lookup as trusted merely because it was
listed here.
-/

namespace Ix.Tc

/-! ## Lookup authority -/

/-- Why the checker is reading a constant. The role, not mere presence in the
loaded catalog cache, determines whether the read has semantic authority. -/
inductive ConstLookupRole where
  | subject
  | blockPeer
  | semantic
  deriving Repr, DecidableEq

/-- Per-check subject scope. `targets` is the declaration/block being checked;
`peers` is empty for a standalone and contains exactly an atomic block's
members for a coordinated check. -/
structure LookupScope where
  targets : KId .anon → Prop
  peers : KId .anon → Prop

namespace LookupScope

def standalone (target : KId .anon) : LookupScope where
  targets := fun id => id = target
  peers := fun _ => False

/-- Lookup policy used by the proof. A loaded entry alone is never enough. -/
def Allows (scope : LookupScope) (world : VerifyWorld)
    (role : ConstLookupRole) (id : KId .anon) : Prop :=
  match role with
  | .subject => scope.targets id
  | .blockPeer => scope.peers id
  | .semantic => world.trusted id

@[simp] theorem standalone_subject (target : KId .anon) :
    (standalone target).Allows world .subject target := rfl

@[simp] theorem standalone_no_peer (target id : KId .anon) :
    ¬(standalone target).Allows world .blockPeer id := fun h => h

end LookupScope

/-- The pending target can be acquired as the subject, but cannot be used by
inference, delta unfolding, definitional equality, or a semantic cache hit. -/
theorem PendingDecl.lookup_isolation {trProj : RawProjRel}
    {world : VerifyWorld} {target : KId .anon} {d : Lean4Lean.VDecl}
    (h : PendingDecl trProj world target d) :
    (LookupScope.standalone target).Allows world .subject target ∧
      ¬(LookupScope.standalone target).Allows world .semantic target := by
  obtain ⟨_, _, _, huntrusted, _, _⟩ := h
  exact ⟨rfl, huntrusted⟩

/-! ## Physical cache inventory -/

/-- The seven `(expression address, context address) ↦ expression` maps. -/
inductive ExprCacheKind where
  | whnf
  | whnfNoDelta
  | whnfNoDeltaCheap
  | whnfCore
  | whnfCoreCheap
  | infer
  | inferOnly
  deriving Repr, DecidableEq

/-- The two general defeq result maps. The narrow negative cache has its own
`CacheEntry.defEqFailure` tag because it stores set membership, not a Bool. -/
inductive DefEqCacheKind where
  | full
  | cheap
  deriving Repr, DecidableEq

/-- A typed, exhaustive view of every semantic `KEnv` cache entry.

`ctxAddrCache` and `equivManager` live on `TcState`, are per-check, and are
handled by `TcM.reset`; the lazy-fault set is ingress bookkeeping rather than
a semantic memo. -/
inductive CacheEntry where
  | expr (kind : ExprCacheKind) (key : Address × Address)
      (value : KExpr .anon)
  | defEq (kind : DefEqCacheKind)
      (key : Address × Address × Address) (value : Bool)
  | defEqFailure (key : Address × Address × Address)
  | unfold (key : Address) (value : KExpr .anon)
  | natSuccStuck (key : Address × Address)
  | isProp (key : Address × Address) (value : Bool)
  | isRec (ind : Address) (value : Bool)
  | recursor (block : KId .anon) (value : Array (GeneratedRecursor .anon))
  | recMajors (majors : Array (KId .anon)) (block : KId .anon)
  | blockPeer (block : KId .anon)
  | blockResult (block : KId .anon) (value : Except (TcError .anon) Unit)

/-- Physical membership of a tagged entry in the corresponding `KEnv` field.
There is intentionally one constructor per field/read mode. -/
inductive KEnv.HasCacheEntry (env : KEnv .anon) : CacheEntry → Prop
  | whnf {key value} : env.whnfCache[key]? = some value →
      HasCacheEntry env (.expr .whnf key value)
  | whnfNoDelta {key value} : env.whnfNoDeltaCache[key]? = some value →
      HasCacheEntry env (.expr .whnfNoDelta key value)
  | whnfNoDeltaCheap {key value} :
      env.whnfNoDeltaCheapCache[key]? = some value →
      HasCacheEntry env (.expr .whnfNoDeltaCheap key value)
  | whnfCore {key value} : env.whnfCoreCache[key]? = some value →
      HasCacheEntry env (.expr .whnfCore key value)
  | whnfCoreCheap {key value} :
      env.whnfCoreCheapCache[key]? = some value →
      HasCacheEntry env (.expr .whnfCoreCheap key value)
  | infer {key value} : env.inferCache[key]? = some value →
      HasCacheEntry env (.expr .infer key value)
  | inferOnly {key value} : env.inferOnlyCache[key]? = some value →
      HasCacheEntry env (.expr .inferOnly key value)
  | defEq {key value} : env.defEqCache[key]? = some value →
      HasCacheEntry env (.defEq .full key value)
  | defEqCheap {key value} : env.defEqCheapCache[key]? = some value →
      HasCacheEntry env (.defEq .cheap key value)
  | defEqFailure {key} : env.defEqFailure.contains key = true →
      HasCacheEntry env (.defEqFailure key)
  | unfold {key value} : env.unfoldCache[key]? = some value →
      HasCacheEntry env (.unfold key value)
  | natSuccStuck {key} : env.natSuccStuck.contains key = true →
      HasCacheEntry env (.natSuccStuck key)
  | isProp {key value} : env.isPropCache[key]? = some value →
      HasCacheEntry env (.isProp key value)
  | isRec {ind value} : env.isRecCache[ind]? = some value →
      HasCacheEntry env (.isRec ind value)
  | recursor {block value} : env.recursorCache[block]? = some value →
      HasCacheEntry env (.recursor block value)
  | recMajors {majors block} : env.recMajorsCache[majors]? = some block →
      HasCacheEntry env (.recMajors majors block)
  | blockPeer {block} : env.blockPeerAgreementCache.contains block = true →
      HasCacheEntry env (.blockPeer block)
  | blockResult {block value} : env.blockCheckResults[block]? = some value →
      HasCacheEntry env (.blockResult block value)

/-! ## Finite support and direct dependency provenance -/

namespace RunSupport

/-- An expression in the finite collision scope has this semantic address. -/
def HasExprAddr (support : RunSupport) (addr : Address) : Prop :=
  ∃ e, support e ∧ e.addr = addr

theorem HasExprAddr.mono {small large : RunSupport} (hle : small ≤ large)
    {addr : Address} (h : small.HasExprAddr addr) :
    large.HasExprAddr addr := by
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, hle.1 e he, rfl⟩

end RunSupport

namespace CacheEntry

/-- Cache kinds allowed to depend on the active atomic block. No reduction,
inference, defeq, unfold, stuck, or is-prop entry is subject-scoped. -/
def SubjectScoped : CacheEntry → Prop
  | .isRec .. | .recursor .. | .recMajors .. | .blockPeer .. |
      .blockResult .. => True
  | _ => False

/-- Every expression address observed by a cache key has a source witness in
the finite collision scope, and every cached expression value is in it too. -/
def SupportedBy (support : RunSupport) : CacheEntry → Prop
  | .expr _ key value => support.HasExprAddr key.1 ∧ support value
  | .defEq _ key _ | .defEqFailure key =>
      support.HasExprAddr key.1 ∧ support.HasExprAddr key.2.1
  | .unfold key value => support.HasExprAddr key ∧ support value
  | .natSuccStuck key | .isProp key _ => support.HasExprAddr key.1
  | .recursor _ value =>
      ∀ generated ∈ value, support generated.ty ∧
        ∀ rule ∈ generated.rules, support rule.rhs
  | .isRec .. | .recMajors .. | .blockPeer .. | .blockResult .. => True

theorem SupportedBy.mono {small large : RunSupport} (hle : small ≤ large)
    {entry : CacheEntry} (h : entry.SupportedBy small) :
    entry.SupportedBy large := by
  cases entry with
  | expr kind key value =>
    exact ⟨RunSupport.HasExprAddr.mono hle h.1, hle.1 value h.2⟩
  | defEq kind key value | defEqFailure key =>
    exact ⟨RunSupport.HasExprAddr.mono hle h.1,
      RunSupport.HasExprAddr.mono hle h.2⟩
  | unfold key value =>
    exact ⟨RunSupport.HasExprAddr.mono hle h.1, hle.1 value h.2⟩
  | natSuccStuck key | isProp key value =>
    exact RunSupport.HasExprAddr.mono hle h
  | recursor block value =>
    intro generated hgenerated
    have hg := h generated hgenerated
    exact ⟨hle.1 generated.ty hg.1,
      fun rule hrule => hle.1 rule.rhs (hg.2 rule hrule)⟩
  | isRec | recMajors | blockPeer | blockResult => trivial

/-- A source expression under an address key directly references `id`. The
existential source is ghost provenance lost by the concrete address-only map. -/
def SourceReferences (support : RunSupport) (addr : Address)
    (id : KId .anon) : Prop :=
  ∃ e, support e ∧ e.addr = addr ∧ e.References id

theorem SourceReferences.mono {small large : RunSupport}
    (hle : small ≤ large) {addr : Address} {id : KId .anon}
    (h : SourceReferences small addr id) :
    SourceReferences large addr id := by
  obtain ⟨e, he, ha, href⟩ := h
  exact ⟨e, hle.1 e he, ha, href⟩

/-- Direct constant roots on which an entry can depend. Trusted constants'
own bodies are justified by their trusted-world provenance, so this records
roots rather than an unbounded syntactic transitive closure. -/
def References (support : RunSupport) : CacheEntry → KId .anon → Prop
  | .expr _ key value, id =>
      SourceReferences support key.1 id ∨ value.References id
  | .defEq _ key _, id | .defEqFailure key, id =>
      SourceReferences support key.1 id ∨
        SourceReferences support key.2.1 id
  | .unfold key value, id =>
      SourceReferences support key id ∨ value.References id
  | .natSuccStuck key, id | .isProp key _, id =>
      SourceReferences support key.1 id
  | .isRec ind _, id => id.addr = ind
  | .recursor block generated, id =>
      id = block ∨ ∃ g ∈ generated,
        id.addr = g.indAddr ∨ g.ty.References id ∨
          ∃ rule ∈ g.rules, rule.rhs.References id
  | .recMajors majors block, id => id ∈ majors ∨ id = block
  | .blockPeer block, id => id = block
  | .blockResult block (.ok ()), id => id = block
  | .blockResult _ (.error _), _ => False

theorem References.mono {small large : RunSupport} (hle : small ≤ large)
    {entry : CacheEntry} {id : KId .anon} (h : entry.References small id) :
    entry.References large id := by
  cases entry with
  | expr kind key value =>
    exact h.elim (fun h => .inl (SourceReferences.mono hle h)) .inr
  | defEq kind key value | defEqFailure key =>
    exact h.elim (fun h => .inl (SourceReferences.mono hle h))
      (fun h => .inr (SourceReferences.mono hle h))
  | unfold key value =>
    exact h.elim (fun h => .inl (SourceReferences.mono hle h)) .inr
  | natSuccStuck key | isProp key value =>
    exact SourceReferences.mono hle h
  | isRec | recursor | recMajors | blockPeer => exact h
  | blockResult block value =>
    cases value with
    | ok => exact h
    | error => exact False.elim h

end CacheEntry

/-! ## World/active-block authority and semantic contracts -/

/-- Semantic authority under which cache entries are being used. `active` is
proof-only and is empty at stable top-level boundaries. -/
structure CacheAuthority where
  world : VerifyWorld
  active : KId .anon → Prop

namespace CacheAuthority

def stable (world : VerifyWorld) : CacheAuthority :=
  ⟨world, fun _ => False⟩

protected structure LE (before after : CacheAuthority) : Prop where
  world : before.world ≤ after.world
  authorized : ∀ {id},
    before.world.trusted id ∨ before.active id →
      after.world.trusted id ∨ after.active id

instance : LE CacheAuthority := ⟨CacheAuthority.LE⟩

namespace LE

theorem rfl {authority : CacheAuthority} : authority ≤ authority :=
  ⟨VerifyWorld.LE.rfl, fun h => h⟩

theorem trans {a b c : CacheAuthority} (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c :=
  ⟨hab.world.trans hbc.world, fun h => hbc.authorized (hab.authorized h)⟩

end LE

theorem stable_mono {before after : VerifyWorld} (hle : before ≤ after) :
    stable before ≤ stable after := by
  refine ⟨hle, ?_⟩
  rintro id (h | h)
  · exact .inl (hle.trusted h)
  · exact False.elim h

end CacheAuthority

/-- All direct roots of an entry have the authority appropriate to its kind.
Active-block authority is unavailable to every reduction/inference kind. -/
def CacheEntry.ReferencesAuthorized (authority : CacheAuthority)
    (support : RunSupport) (entry : CacheEntry) : Prop :=
  ∀ ⦃id⦄, entry.References support id →
    authority.world.trusted id ∨
      (entry.SubjectScoped ∧ authority.active id)

/-- The semantic meaning of each tagged cache family. K1/K2 provide the
concrete `Valid`; G4 requires world monotonicity so a warm entry remains
usable after declarations are admitted. A composite run chooses its final
finite support up front, so changing support is deliberately not hidden in
this interface. -/
structure CacheSemantics where
  Valid : CacheAuthority → RunSupport → CacheEntry → Prop
  mono : ∀ {before after : CacheAuthority} {support : RunSupport}
    {entry : CacheEntry}, before ≤ after →
      Valid before support entry → Valid after support entry
  blockError : ∀ (authority : CacheAuthority) (support : RunSupport)
    (block : KId .anon) (err : TcError .anon),
      Valid authority support (.blockResult block (.error err))

/-- Full ghost certificate attached to one physical entry. -/
structure CacheProvenance (semantics : CacheSemantics)
    (authority : CacheAuthority) (support : RunSupport)
    (entry : CacheEntry) : Prop where
  supported : entry.SupportedBy support
  references : entry.ReferencesAuthorized authority support
  valid : semantics.Valid authority support entry

namespace CacheProvenance

/-- Cached failures carry no acceptance claim, have no expression support or
constant dependencies, and are valid under every cache contract. -/
theorem blockError (semantics : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) (block : KId .anon) (err : TcError .anon) :
    CacheProvenance semantics authority support
      (.blockResult block (.error err)) := by
  refine ⟨trivial, ?_, semantics.blockError authority support block err⟩
  intro id href
  exact False.elim href

theorem mono {semantics : CacheSemantics}
    {before after : CacheAuthority} {support : RunSupport}
    {entry : CacheEntry} (hauth : before ≤ after)
    (h : CacheProvenance semantics before support entry) :
    CacheProvenance semantics after support entry := by
  refine ⟨h.supported, ?_, semantics.mono hauth h.valid⟩
  intro id href
  have hold := h.references href
  rcases hold with htrusted | ⟨hsubject, hactive⟩
  · exact .inl (hauth.world.trusted htrusted)
  · exact (hauth.authorized (.inr hactive)).elim .inl
      (fun h => .inr ⟨hsubject, h⟩)

/-- A semantic (non-block-scoped) cache entry cannot depend directly on a
pending target. This is the cache-hit half of the self-unfolding barrier. -/
theorem pending_isolation {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport} {entry : CacheEntry}
    {trProj : RawProjRel} {target : KId .anon} {d : Lean4Lean.VDecl}
    (hpending : PendingDecl trProj authority.world target d)
    (hentry : ¬entry.SubjectScoped)
    (h : CacheProvenance semantics authority support entry) :
    ¬entry.References support target := by
  obtain ⟨_, _, _, huntrusted, _, _⟩ := hpending
  intro href
  rcases h.references href with htrusted | hactive
  · exact huntrusted htrusted
  · exact hentry hactive.1

/-- At a stable boundary even structural block entries cannot name a pending
target: there is no active-block authority left. -/
theorem pending_isolation_stable {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport} {entry : CacheEntry}
    {trProj : RawProjRel} {target : KId .anon} {d : Lean4Lean.VDecl}
    (hstable : ∀ id, ¬authority.active id)
    (hpending : PendingDecl trProj authority.world target d)
    (h : CacheProvenance semantics authority support entry) :
    ¬entry.References support target := by
  obtain ⟨_, _, _, huntrusted, _, _⟩ := hpending
  intro href
  rcases h.references href with htrusted | hactive
  · exact huntrusted htrusted
  · exact hstable target hactive.2

end CacheProvenance

namespace KEnv

/-- Every block verdict surviving error restoration is either the exact old
verdict or an error. In particular, a failed check cannot synthesize a new
cached success or replace an old verdict. -/
theorem restoreBlockCheckResultsOnError_origin
    (before after : Std.HashMap (KId .anon)
      (Except (TcError .anon) Unit))
    {block : KId .anon} {result : Except (TcError .anon) Unit}
    (h : (restoreBlockCheckResultsOnError before after)[block]? =
      some result) :
    before[block]? = some result ∨
      ∃ err, result = .error err := by
  let step := fun
      (results : Std.HashMap (KId .anon) (Except (TcError .anon) Unit))
      (item : KId .anon × Except (TcError .anon) Unit) =>
    restoreBlockCheckResultOnError before results item.1 item.2
  rw [restoreBlockCheckResultsOnError,
    Std.HashMap.fold_eq_foldl_toList] at h
  have hstep :
      (List.foldl step before after.toList)[block]? = some result := by
    simpa only [step] using h
  have hinv : ∀ (results :
      Std.HashMap (KId .anon) (Except (TcError .anon) Unit)),
      (∀ {key : KId .anon} {value : Except (TcError .anon) Unit},
        results[key]? = some value →
          before[key]? = some value ∨
            ∃ err : TcError .anon, value = Except.error err) →
      ∀ {item : KId .anon × Except (TcError .anon) Unit},
        item ∈ after.toList →
        ∀ {key : KId .anon} {value : Except (TcError .anon) Unit},
          (step results item)[key]? = some value →
            before[key]? = some value ∨
              ∃ err : TcError .anon, value = Except.error err := by
    intro results ih item _ key value hget
    rcases item with ⟨newKey, newValue⟩
    cases newValue with
    | ok okValue =>
      cases okValue
      exact ih hget
    | error err =>
      dsimp [step, restoreBlockCheckResultOnError] at hget
      split at hget
      · exact ih hget
      · rw [Std.HashMap.getElem?_insert] at hget
        split at hget
        · cases hget
          exact .inr ⟨err, rfl⟩
        · exact ih hget
  have hall : ∀ {key : KId .anon}
      {value : Except (TcError .anon) Unit},
      (List.foldl step before after.toList)[key]? = some value →
        before[key]? = some value ∨
          ∃ err : TcError .anon, value = Except.error err := by
    apply List.foldlRecOn (motive := fun results =>
      ∀ {key : KId .anon} {value : Except (TcError .anon) Unit},
        results[key]? = some value →
          before[key]? = some value ∨
            ∃ err : TcError .anon, value = Except.error err)
      after.toList step
    · intro key value hget
      exact .inl hget
    · exact hinv
  exact hall hstep

end KEnv

/-- Every physical cache entry has finite-support, dependency, and semantic
provenance. -/
def CacheInvariant (semantics : CacheSemantics)
    (authority : CacheAuthority) (support : RunSupport)
    (env : KEnv .anon) : Prop :=
  ∀ ⦃entry⦄, env.HasCacheEntry entry →
    CacheProvenance semantics authority support entry

namespace CacheInvariant

/-- A concrete hit exposes its recorded semantic provenance. -/
theorem hit {semantics : CacheSemantics} {authority : CacheAuthority}
    {support : RunSupport} {env : KEnv .anon} {entry : CacheEntry}
    (h : CacheInvariant semantics authority support env)
    (hhit : env.HasCacheEntry entry) :
    CacheProvenance semantics authority support entry :=
  h hhit

/-- Warm entries transport when the trusted world grows. -/
theorem mono {semantics : CacheSemantics}
    {before after : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} (hauth : before ≤ after)
    (h : CacheInvariant semantics before support env) :
    CacheInvariant semantics after support env := by
  intro entry hentry
  exact (h hentry).mono hauth

/-- A fresh kernel environment satisfies every semantic cache contract. -/
theorem empty (semantics : CacheSemantics) (authority : CacheAuthority)
    (support : RunSupport) :
    CacheInvariant semantics authority support ({} : KEnv .anon) := by
  intro entry h
  cases h <;> simp_all

/-- Extensional fresh-cache constructor for an environment that may already
contain constants, blocks, and interned nodes. -/
theorem of_no_entries {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport} {env : KEnv .anon}
    (h : ∀ entry, ¬env.HasCacheEntry entry) :
    CacheInvariant semantics authority support env := by
  intro entry hentry
  exact False.elim (h entry hentry)

/-- Generic cache-update rule. Concrete insertion proofs need only show that
each post-entry is either the newly certified entry or an old hit. -/
theorem update {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {before after : KEnv .anon} {newEntry : CacheEntry}
    (hbefore : CacheInvariant semantics authority support before)
    (hnew : CacheProvenance semantics authority support newEntry)
    (hentries : ∀ ⦃entry⦄, after.HasCacheEntry entry →
      entry = newEntry ∨ before.HasCacheEntry entry) :
    CacheInvariant semantics authority support after := by
  intro entry hentry
  rcases hentries hentry with rfl | hold
  · exact hnew
  · exact hbefore hold

/-- Insert one certified full-whnf result while retaining provenance for all
old entries.  The four policy-specific siblings below cover every other K1
WHNF expression map; their exact semantic payload is supplied by
`Verify/Whnf.lean`. -/
theorem insertWhnf {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {key : Address × Address} {value : KExpr .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.expr .whnf key value)) :
    CacheInvariant semantics authority support
      { env with whnfCache := env.whnfCache.insert key value } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | @whnf foundKey foundValue hget =>
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · next heq =>
      cases hget
      have hkey : key = foundKey := eq_of_beq heq
      subst foundKey
      exact .inl rfl
    · exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Insert one certified full-policy no-delta result. -/
theorem insertWhnfNoDelta {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {key : Address × Address} {value : KExpr .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.expr .whnfNoDelta key value)) :
    CacheInvariant semantics authority support
      { env with
        whnfNoDeltaCache := env.whnfNoDeltaCache.insert key value } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | @whnfNoDelta foundKey foundValue hget =>
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · next heq =>
      cases hget
      have hkey : key = foundKey := eq_of_beq heq
      subst foundKey
      exact .inl rfl
    · exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Insert one certified cheap-policy no-delta result.  Its tag is distinct
from the full-policy map, preventing a cheap result from being consumed as a
full result. -/
theorem insertWhnfNoDeltaCheap {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {key : Address × Address} {value : KExpr .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.expr .whnfNoDeltaCheap key value)) :
    CacheInvariant semantics authority support
      { env with
        whnfNoDeltaCheapCache :=
          env.whnfNoDeltaCheapCache.insert key value } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | @whnfNoDeltaCheap foundKey foundValue hget =>
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · next heq =>
      cases hget
      have hkey : key = foundKey := eq_of_beq heq
      subst foundKey
      exact .inl rfl
    · exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Insert one certified full structural-WHNF result. -/
theorem insertWhnfCore {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {key : Address × Address} {value : KExpr .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.expr .whnfCore key value)) :
    CacheInvariant semantics authority support
      { env with whnfCoreCache := env.whnfCoreCache.insert key value } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | @whnfCore foundKey foundValue hget =>
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · next heq =>
      cases hget
      have hkey : key = foundKey := eq_of_beq heq
      subst foundKey
      exact .inl rfl
    · exact .inr (.whnfCore hget)
  | whnfCoreCheap hget => exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Insert one certified cheap structural-WHNF result. -/
theorem insertWhnfCoreCheap {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {key : Address × Address} {value : KExpr .anon}
    (hbefore : CacheInvariant semantics authority support env)
    (hnew : CacheProvenance semantics authority support
      (.expr .whnfCoreCheap key value)) :
    CacheInvariant semantics authority support
      { env with
        whnfCoreCheapCache := env.whnfCoreCheapCache.insert key value } := by
  apply update hbefore hnew
  intro entry hentry
  cases hentry with
  | whnf hget => exact .inr (.whnf hget)
  | whnfNoDelta hget => exact .inr (.whnfNoDelta hget)
  | whnfNoDeltaCheap hget => exact .inr (.whnfNoDeltaCheap hget)
  | whnfCore hget => exact .inr (.whnfCore hget)
  | @whnfCoreCheap foundKey foundValue hget =>
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · next heq =>
      cases hget
      have hkey : key = foundKey := eq_of_beq heq
      subst foundKey
      exact .inl rfl
    · exact .inr (.whnfCoreCheap hget)
  | infer hget => exact .inr (.infer hget)
  | inferOnly hget => exact .inr (.inferOnly hget)
  | defEq hget => exact .inr (.defEq hget)
  | defEqCheap hget => exact .inr (.defEqCheap hget)
  | defEqFailure hmem => exact .inr (.defEqFailure hmem)
  | unfold hget => exact .inr (.unfold hget)
  | natSuccStuck hmem => exact .inr (.natSuccStuck hmem)
  | isProp hget => exact .inr (.isProp hget)
  | isRec hget => exact .inr (.isRec hget)
  | recursor hget => exact .inr (.recursor hget)
  | recMajors hget => exact .inr (.recMajors hget)
  | blockPeer hmem => exact .inr (.blockPeer hmem)
  | blockResult hget => exact .inr (.blockResult hget)

/-- Exact environment equality preserves all cache provenance. -/
theorem of_env_eq {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {before after : KEnv .anon} (h : CacheInvariant semantics authority support before)
    (heq : after = before) : CacheInvariant semantics authority support after :=
  heq ▸ h

/-- Intern-table growth does not touch any semantic cache field. -/
theorem of_intern_update {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {env : KEnv .anon} {intern : InternTable .anon}
    (h : CacheInvariant semantics authority support env) :
    CacheInvariant semantics authority support { env with intern } := by
  intro entry hentry
  apply h
  cases hentry with
  | whnf hget => exact .whnf hget
  | whnfNoDelta hget => exact .whnfNoDelta hget
  | whnfNoDeltaCheap hget => exact .whnfNoDeltaCheap hget
  | whnfCore hget => exact .whnfCore hget
  | whnfCoreCheap hget => exact .whnfCoreCheap hget
  | infer hget => exact .infer hget
  | inferOnly hget => exact .inferOnly hget
  | defEq hget => exact .defEq hget
  | defEqCheap hget => exact .defEqCheap hget
  | defEqFailure hmem => exact .defEqFailure hmem
  | unfold hget => exact .unfold hget
  | natSuccStuck hmem => exact .natSuccStuck hmem
  | isProp hget => exact .isProp hget
  | isRec hget => exact .isRec hget
  | recursor hget => exact .recursor hget
  | recMajors hget => exact .recMajors hget
  | blockPeer hmem => exact .blockPeer hmem
  | blockResult hget => exact .blockResult hget

/-- Periodic reduction-cache clearing removes entries and cannot invalidate
the retained structural/block entries. -/
theorem clearReductionCaches {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport} {env : KEnv .anon}
    (h : CacheInvariant semantics authority support env) :
    CacheInvariant semantics authority support env.clearReductionCaches := by
  intro entry hentry
  cases hentry with
  | @whnf key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @whnfNoDelta key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @whnfNoDeltaCheap key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @whnfCore key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @whnfCoreCheap key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @infer key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @inferOnly key value hget =>
    change ({} : Std.HashMap (Address × Address) (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @defEq key value hget =>
    change ({} : Std.HashMap (Address × Address × Address) Bool)[key]? = _ at hget
    simp at hget
  | @defEqCheap key value hget =>
    change ({} : Std.HashMap (Address × Address × Address) Bool)[key]? = _ at hget
    simp at hget
  | @defEqFailure key hmem =>
    change ({} : Std.HashSet (Address × Address × Address)).contains key = true at hmem
    simp at hmem
  | @unfold key value hget =>
    change ({} : Std.HashMap Address (KExpr .anon))[key]? = _ at hget
    simp at hget
  | @natSuccStuck key hmem =>
    change ({} : Std.HashSet (Address × Address)).contains key = true at hmem
    simp at hmem
  | @isProp key value hget =>
    change ({} : Std.HashMap (Address × Address) Bool)[key]? = _ at hget
    simp at hget
  | isRec hget => exact h (.isRec hget)
  | recursor hget => exact h (.recursor hget)
  | recMajors hget => exact h (.recMajors hget)
  | blockPeer hmem => exact h (.blockPeer hmem)
  | blockResult hget => exact h (.blockResult hget)

/-- Error restoration preserves the complete cache invariant without any
assumption about cache entries created by the failed run. All semantic and
subject-scoped entries revert to `before`; the only new retained entries are
cached errors, whose contract and dependency set are unconditional. -/
theorem restoreCheckCachesOnError {semantics : CacheSemantics}
    {authority : CacheAuthority} {support : RunSupport}
    {before after : KEnv .anon}
    (hbefore : CacheInvariant semantics authority support before) :
    CacheInvariant semantics authority support
      (before.restoreCheckCachesOnError after) := by
  intro entry hentry
  cases hentry with
  | whnf hget =>
    exact hbefore (.whnf (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | whnfNoDelta hget =>
    exact hbefore (.whnfNoDelta (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | whnfNoDeltaCheap hget =>
    exact hbefore (.whnfNoDeltaCheap (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | whnfCore hget =>
    exact hbefore (.whnfCore (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | whnfCoreCheap hget =>
    exact hbefore (.whnfCoreCheap (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | infer hget =>
    exact hbefore (.infer (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | inferOnly hget =>
    exact hbefore (.inferOnly (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | defEq hget =>
    exact hbefore (.defEq (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | defEqCheap hget =>
    exact hbefore (.defEqCheap (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | defEqFailure hmem =>
    exact hbefore (.defEqFailure (by
      simpa [KEnv.restoreCheckCachesOnError] using hmem))
  | unfold hget =>
    exact hbefore (.unfold (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | natSuccStuck hmem =>
    exact hbefore (.natSuccStuck (by
      simpa [KEnv.restoreCheckCachesOnError] using hmem))
  | isProp hget =>
    exact hbefore (.isProp (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | isRec hget =>
    exact hbefore (.isRec (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | recursor hget =>
    exact hbefore (.recursor (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | recMajors hget =>
    exact hbefore (.recMajors (by
      simpa [KEnv.restoreCheckCachesOnError] using hget))
  | blockPeer hmem =>
    exact hbefore (.blockPeer (by
      simpa [KEnv.restoreCheckCachesOnError] using hmem))
  | @blockResult block value hget =>
    change (KEnv.restoreBlockCheckResultsOnError
      before.blockCheckResults after.blockCheckResults)[block]? =
        some value at hget
    rcases KEnv.restoreBlockCheckResultsOnError_origin _ _ hget with
      hold | ⟨err, rfl⟩
    · exact hbefore (.blockResult hold)
    · exact CacheProvenance.blockError semantics authority support block err

end CacheInvariant

/-! ## Concrete error/reset equations -/

namespace KEnv

@[simp] theorem restoreCheckCachesOnError_whnfCache
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).whnfCache = before.whnfCache := rfl

@[simp] theorem restoreCheckCachesOnError_inferCache
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).inferCache = before.inferCache := rfl

@[simp] theorem restoreCheckCachesOnError_defEqCache
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).defEqCache = before.defEqCache := rfl

@[simp] theorem restoreCheckCachesOnError_unfoldCache
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).unfoldCache = before.unfoldCache := rfl

@[simp] theorem restoreCheckCachesOnError_isRecCache
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).isRecCache = before.isRecCache := rfl

@[simp] theorem restoreCheckCachesOnError_recursorCache
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).recursorCache =
      before.recursorCache := rfl

/-- Cache rollback never rolls back loaded constants. -/
@[simp] theorem restoreCheckCachesOnError_consts
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).consts = after.consts := rfl

/-- Cache rollback never rolls back the intern table. -/
@[simp] theorem restoreCheckCachesOnError_intern
    (before after : KEnv m) :
    (restoreCheckCachesOnError before after).intern = after.intern := rfl

end KEnv

namespace TcM

theorem isolateCheckErrors_ok {x : TcM m α} {s s' : TcState m} {a : α}
    (h : x s = .ok a s') :
    isolateCheckErrors x s = .ok a s' := by
  simp [isolateCheckErrors, h]

theorem isolateCheckErrors_error {x : TcM m α} {s s' : TcState m}
    {err : TcError m} (h : x s = .error err s') :
    isolateCheckErrors x s =
      .error err (s.restoreCheckCachesOnError s') := by
  simp [isolateCheckErrors, h]

/-- `reset` leaves all environment-level warm caches untouched, while clearing
the two per-check memo structures. -/
theorem reset_cache_frame (s : TcState m) :
    match TcM.reset s with
    | .ok () s' => s'.env = s.env ∧ s'.equivManager = {} ∧
        s'.ctxAddrCache = {}
    | .error _ _ => False := by
  change s.env = s.env ∧ ({} : EquivManager) = {} ∧
    ({} : Std.HashMap (Address × UInt64) Address) = {}
  exact ⟨rfl, rfl, rfl⟩

end TcM

end Ix.Tc
