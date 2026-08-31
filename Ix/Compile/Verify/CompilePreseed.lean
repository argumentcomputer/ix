import Ix.Compile.Verify.CompileConstantCodec
import Lean4Lean.Verify.QSort

/-!
# Production expression-table preseeding

This module verifies the total phase decomposition exposed by
`Ix.CompileM.preseedExprTables`.  The first layer covers canonical-universe
memoization and records the unconditional finalization flag.  Subsequent
layers establish the sorted reference/universe commits and connect collection
of an ordinary source expression to the frozen compiler context.
-/

namespace Ix.Compile.Verify

local instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

local instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

local instance : LawfulHashable Address where
  hash_eq left right h := by rw [eq_of_beq h]

private theorem run_bind (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (action : Ix.CompileM.CompileM α)
    (next : α → Ix.CompileM.CompileM β) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (action >>= next) =
      match Ix.CompileM.CompileM.run compileEnv blockEnv state action with
      | .error err => .error err
      | .ok (value, state') =>
        Ix.CompileM.CompileM.run compileEnv blockEnv state' (next value) := by
  simp [Ix.CompileM.CompileM.run, ReaderT.run_bind, ExceptT.run_bind,
    StateT.run_bind]
  generalize
    (ReaderT.run action (compileEnv, blockEnv)).run.run state = result
  rcases result with ⟨result, state'⟩
  cases result <;> rfl

private theorem run_getCompileEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getCompileEnv = .ok (compileEnv, state) := by
  rfl

private theorem run_getBlockState (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getBlockState = .ok (state, state) := by
  rfl

private theorem run_getBlockEnv (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        Ix.CompileM.getBlockEnv = .ok (blockEnv, state) := by
  rfl

private theorem run_discard_internRef
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (addr : Address) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (discard <| Ix.CompileM.internRef addr) =
      .ok ((), (state.internRef addr).1) := by
  rfl

private theorem run_discard_internUniv
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (u : Ixon.Univ) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (discard <| Ix.CompileM.internUniv u) =
      .ok ((), (state.internUniv u).1) := by
  rfl

private theorem internRef_own_index
    (state : Ix.CompileM.BlockState) (addr : Address) :
    let (state', idx) := state.internRef addr
    state'.refsIndex.get? addr = some idx := by
  simp only [Ix.CompileM.BlockState.internRef]
  split
  next idx hindex => exact hindex
  next hmissing => simp

private theorem internRef_preserves_index
    (state : Ix.CompileM.BlockState) (addr queried : Address) (idx : UInt64)
    (hget : state.refsIndex.get? queried = some idx) :
    let state' := (state.internRef addr).1
    state'.refsIndex.get? queried = some idx := by
  simp only [Ix.CompileM.BlockState.internRef]
  split
  next found hfound => exact hget
  next hmissing =>
    simp only [Std.HashMap.get?_insert]
    split
    next heq =>
      have hqueried : queried = addr := (eq_of_beq heq).symm
      subst queried
      rw [hmissing] at hget
      contradiction
    next hne => exact hget

private theorem internUniv_own_index
    (state : Ix.CompileM.BlockState) (u : Ixon.Univ) :
    let (state', idx) := state.internUniv u
    state'.univsIndex.get? u = some idx := by
  simp only [Ix.CompileM.BlockState.internUniv]
  split
  next idx hindex => exact hindex
  next hmissing => simp

private theorem internUniv_preserves_index
    (state : Ix.CompileM.BlockState) (u queried : Ixon.Univ) (idx : UInt64)
    (hget : state.univsIndex.get? queried = some idx) :
    let state' := (state.internUniv u).1
    state'.univsIndex.get? queried = some idx := by
  simp only [Ix.CompileM.BlockState.internUniv]
  split
  next found hfound => exact hget
  next hmissing =>
    simp only [Std.HashMap.get?_insert]
    split
    next heq =>
      have hqueried : queried = u := (eq_of_beq heq).symm
      subst queried
      rw [hmissing] at hget
      contradiction
    next hne => exact hget

/-- State facts preserved while the preseed collector walks source syntax.
Only the context-sensitive universe memo and blob store may grow; the primary
tables, expression cache, canonical memo, and arena retain their origin view. -/
structure PreseedCollectStateWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (origin state : Ix.CompileM.BlockState) : Prop where
  tables : exprTableView state = exprTableView origin
  exprCache : state.exprCache = origin.exprCache
  univCache : UnivCacheWF
    (univParamIndex blockEnv.univCtx) levelSupport state
  canonUnivCache : CanonUnivCacheWF state
  arena : state.arena = origin.arena

/-- Context-independent portion of the collector frame. The sorted commit
tail never reads the last root's context-sensitive universe memo, so this is
the exact interface needed by heterogeneous root lists. -/
structure PreseedCollectFrameWF
    (origin state : Ix.CompileM.BlockState) : Prop where
  tables : exprTableView state = exprTableView origin
  exprCache : state.exprCache = origin.exprCache
  canonUnivCache : CanonUnivCacheWF state
  arena : state.arena = origin.arena

theorem PreseedCollectStateWF.frame
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {origin state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    PreseedCollectFrameWF origin state :=
  ⟨hstate.tables, hstate.exprCache, hstate.canonUnivCache, hstate.arena⟩

theorem PreseedCollectStateWF.refl
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (state : Ix.CompileM.BlockState)
    (huniv : UnivCacheWF
      (univParamIndex blockEnv.univCtx) levelSupport state)
    (hcanon : CanonUnivCacheWF state) :
    PreseedCollectStateWF compileEnv blockEnv levelSupport state state :=
  { tables := rfl
    exprCache := rfl
    univCache := huniv
    canonUnivCache := hcanon
    arena := rfl }

private def preseedBlobState (state : Ix.CompileM.BlockState)
    (addr : Address) (bytes : ByteArray) : Ix.CompileM.BlockState :=
  { state with blockBlobs := state.blockBlobs.insert addr bytes }

private theorem PreseedCollectStateWF.blob
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {origin state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) (addr : Address) (bytes : ByteArray) :
    PreseedCollectStateWF compileEnv blockEnv levelSupport origin
      (preseedBlobState state addr bytes) :=
  { tables := hstate.tables
    exprCache := hstate.exprCache
    univCache := hstate.univCache.of_cache_eq rfl
    canonUnivCache := hstate.canonUnivCache.of_cache_eq rfl
    arena := hstate.arena }

private theorem PreseedCollectStateWF.of_compileUniv
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {origin before after : Ix.CompileM.BlockState}
    (hbefore : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin before)
    (huniv : UnivCacheWF
      (univParamIndex blockEnv.univCtx) levelSupport after)
    (htables : exprTableView after = exprTableView before)
    (hexpr : after.exprCache = before.exprCache)
    (hcanon : after.canonUnivCache = before.canonUnivCache)
    (harena : after.arena = before.arena) :
    PreseedCollectStateWF compileEnv blockEnv levelSupport origin after :=
  { tables := htables.trans hbefore.tables
    exprCache := hexpr.trans hbefore.exprCache
    univCache := huniv
    canonUnivCache := hbefore.canonUnivCache.of_cache_eq hcanon
    arena := harena.trans hbefore.arena }

/-- Source-side domain for successful, wire-safe table collection. It
contains ordinary syntax, supported/compilable universes whose canonical
forms fit the universe wire, and 32-byte resolution of every external
constant/projection address. It deliberately does not yet assert that the
eventual sorted tables cover the reference compiler. -/
inductive PreseedReady
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (levelSupport : Ix.Level → Prop)
    (origin : Ix.CompileM.BlockState) : Ix.Expr → Prop where
  | bvar {idx hash} :
      PreseedReady compileEnv blockEnv levelSupport origin (.bvar idx hash)
  | sort {level hash} : levelSupport level →
      (∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) level = some u ∧
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv u)) →
      PreseedReady compileEnv blockEnv levelSupport origin (.sort level hash)
  | const {name levels hash} :
      (∀ level ∈ levels, levelSupport level ∧
        ∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) level = some u ∧
          Codec.Ixon.Univ.WireWF (Ixon.canonUniv u)) →
      (blockEnv.mutCtx.get? name = none →
        ∃ addr, resolveConstAddr? compileEnv origin name = some addr ∧
          addr.hash.size = 32) →
      PreseedReady compileEnv blockEnv levelSupport origin
        (.const name levels hash)
  | app {fn arg hash} :
      PreseedReady compileEnv blockEnv levelSupport origin fn →
      PreseedReady compileEnv blockEnv levelSupport origin arg →
      PreseedReady compileEnv blockEnv levelSupport origin (.app fn arg hash)
  | lam {name ty body bi hash} :
      PreseedReady compileEnv blockEnv levelSupport origin ty →
      PreseedReady compileEnv blockEnv levelSupport origin body →
      PreseedReady compileEnv blockEnv levelSupport origin
        (.lam name ty body bi hash)
  | all {name ty body bi hash} :
      PreseedReady compileEnv blockEnv levelSupport origin ty →
      PreseedReady compileEnv blockEnv levelSupport origin body →
      PreseedReady compileEnv blockEnv levelSupport origin
        (.forallE name ty body bi hash)
  | letE {name ty val body nonDep hash} :
      PreseedReady compileEnv blockEnv levelSupport origin ty →
      PreseedReady compileEnv blockEnv levelSupport origin val →
      PreseedReady compileEnv blockEnv levelSupport origin body →
      PreseedReady compileEnv blockEnv levelSupport origin
        (.letE name ty val body nonDep hash)
  | lit {literal hash} :
      PreseedReady compileEnv blockEnv levelSupport origin (.lit literal hash)
  | proj {typeName field val hash} :
      (∃ addr, resolveConstAddr? compileEnv origin typeName = some addr ∧
        addr.hash.size = 32) →
      PreseedReady compileEnv blockEnv levelSupport origin val →
      PreseedReady compileEnv blockEnv levelSupport origin
        (.proj typeName field val hash)
  | mdata {data inner hash} :
      PreseedReady compileEnv blockEnv levelSupport origin inner →
      PreseedReady compileEnv blockEnv levelSupport origin
        (.mdata data inner hash)

theorem PreseedReady.supported
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {origin : Ix.CompileM.BlockState} {source : Ix.Expr} :
    PreseedReady compileEnv blockEnv levelSupport origin source →
      SupportedOrdinaryExpr levelSupport source
  | .bvar => .bvar
  | .sort hlevel _ => .sort hlevel
  | .const hlevels _ => .const fun level hmem => (hlevels level hmem).1
  | .app hfn harg => .app hfn.supported harg.supported
  | .lam hty hbody => .lam hty.supported hbody.supported
  | .all hty hbody => .all hty.supported hbody.supported
  | .letE hty hval hbody =>
    .letE hty.supported hval.supported hbody.supported
  | .lit => .lit
  | .proj _ hval => .proj hval.supported
  | .mdata hinner => .mdata hinner.supported

/-- Every payload accumulated so far is suitable for its eventual primary
table: addresses have the fixed BLAKE3 width and raw universes canonicalize
into the universe codec's domain. The seen set has no bearing on this local
payload property. -/
structure PreseedCollectionWireWF
    (collection : Ix.CompileM.ExprTableCollection) : Prop where
  refs : ∀ addr ∈ collection.1, addr.hash.size = 32
  univs : ∀ u ∈ collection.2.1,
    Codec.Ixon.Univ.WireWF (Ixon.canonUniv u)

theorem PreseedCollectionWireWF.empty :
    PreseedCollectionWireWF (#[], #[], {}) := by
  constructor <;> intro value hmem
  · exact (Array.not_mem_empty value hmem).elim
  · exact (Array.not_mem_empty value hmem).elim

theorem PreseedCollectionWireWF.withSeen
    {refs : Array Address} {univs : Array Ixon.Univ}
    {seen seen' : Std.HashMap (Address × Address) Unit}
    (h : PreseedCollectionWireWF (refs, univs, seen)) :
    PreseedCollectionWireWF (refs, univs, seen') :=
  ⟨h.refs, h.univs⟩

theorem PreseedCollectionWireWF.pushRef
    {refs : Array Address} {univs : Array Ixon.Univ}
    {seen seen' : Std.HashMap (Address × Address) Unit}
    (h : PreseedCollectionWireWF (refs, univs, seen))
    (addr : Address) (haddr : addr.hash.size = 32) :
    PreseedCollectionWireWF (refs.push addr, univs, seen') := by
  constructor
  · intro value hmem
    simp only [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact h.refs value hmem
    · exact haddr
  · exact h.univs

theorem PreseedCollectionWireWF.pushUniv
    {refs : Array Address} {univs : Array Ixon.Univ}
    {seen seen' : Std.HashMap (Address × Address) Unit}
    (h : PreseedCollectionWireWF (refs, univs, seen))
    (u : Ixon.Univ) (hu : Codec.Ixon.Univ.WireWF (Ixon.canonUniv u)) :
    PreseedCollectionWireWF (refs, univs.push u, seen') := by
  constructor
  · exact h.refs
  · intro value hmem
    simp only [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact h.univs value hmem
    · exact hu

theorem addressBlake3_wire (bytes : ByteArray) :
    (Address.blake3 bytes).hash.size = 32 := by
  exact (Blake3.Rust.hash bytes).property

/-- Conservative number of reference payloads a source walk can append.
Seen-set deduplication can only decrease this cost. -/
def preseedRefCount (mutCtx : Ix.MutCtx) : Ix.Expr → Nat
  | .bvar .. | .fvar .. | .mvar .. | .sort .. => 0
  | .const name _ _ =>
    match mutCtx.get? name with
    | some _ => 0
    | none => 1
  | .app fn arg _ => preseedRefCount mutCtx fn + preseedRefCount mutCtx arg
  | .lam _ ty body _ _ | .forallE _ ty body _ _ =>
    preseedRefCount mutCtx ty + preseedRefCount mutCtx body
  | .letE _ ty value body _ _ =>
    preseedRefCount mutCtx ty + preseedRefCount mutCtx value +
      preseedRefCount mutCtx body
  | .lit .. => 1
  | .proj _ _ value _ => preseedRefCount mutCtx value + 1
  | .mdata _ inner _ => preseedRefCount mutCtx inner

/-- Conservative number of positional universe payloads a source walk can
append before canonicalization. -/
def preseedUnivCount : Ix.Expr → Nat
  | .bvar .. | .fvar .. | .mvar .. | .lit .. => 0
  | .sort .. => 1
  | .const _ levels _ => levels.size
  | .app fn arg _ => preseedUnivCount fn + preseedUnivCount arg
  | .lam _ ty body _ _ | .forallE _ ty body _ _ =>
    preseedUnivCount ty + preseedUnivCount body
  | .letE _ ty value body _ _ =>
    preseedUnivCount ty + preseedUnivCount value + preseedUnivCount body
  | .proj _ _ value _ => preseedUnivCount value
  | .mdata _ inner _ => preseedUnivCount inner

structure PreseedCollectionSizeBound (mutCtx : Ix.MutCtx)
    (source : Ix.Expr) (before after : Ix.CompileM.ExprTableCollection) :
    Prop where
  refs : after.1.size ≤ before.1.size + preseedRefCount mutCtx source
  univs : after.2.1.size ≤ before.2.1.size + preseedUnivCount source

theorem PreseedCollectionSizeBound.same
    (mutCtx : Ix.MutCtx) (source : Ix.Expr)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (seen seen' : Std.HashMap (Address × Address) Unit) :
    PreseedCollectionSizeBound mutCtx source
      (refs, univs, seen) (refs, univs, seen') := by
  constructor <;> dsimp only <;> omega

/-- Conservative accumulated cost of the two same-context roots used by a
non-axiom singleton definition payload. -/
structure PreseedPairCollectionSizeBound (mutCtx : Ix.MutCtx)
    (first second : Ix.Expr)
    (collection : Ix.CompileM.ExprTableCollection) : Prop where
  refs : collection.1.size ≤
    preseedRefCount mutCtx first + preseedRefCount mutCtx second
  univs : collection.2.1.size ≤
    preseedUnivCount first + preseedUnivCount second

def preseedRootRefCount (mutCtx : Ix.MutCtx) : List Ix.Expr → Nat
  | [] => 0
  | source :: rest =>
    preseedRefCount mutCtx source + preseedRootRefCount mutCtx rest

def preseedRootUnivCount : List Ix.Expr → Nat
  | [] => 0
  | source :: rest => preseedUnivCount source + preseedRootUnivCount rest

structure PreseedRootCollectionSizeBound (mutCtx : Ix.MutCtx)
    (sources : List Ix.Expr) (before after : Ix.CompileM.ExprTableCollection) :
    Prop where
  refs : after.1.size ≤ before.1.size + preseedRootRefCount mutCtx sources
  univs : after.2.1.size ≤
    before.2.1.size + preseedRootUnivCount sources

/-- Structural collection cost for roots carrying distinct universe-parameter
contexts. Contexts affect compilation but not the number of visited reference
or universe leaves. -/
def preseedInputRefCount (mutCtx : Ix.MutCtx) :
    List (Ix.Expr × List Ix.Name) → Nat
  | [] => 0
  | (source, _) :: rest =>
    preseedRefCount mutCtx source + preseedInputRefCount mutCtx rest

def preseedInputUnivCount : List (Ix.Expr × List Ix.Name) → Nat
  | [] => 0
  | (source, _) :: rest =>
    preseedUnivCount source + preseedInputUnivCount rest

structure PreseedInputCollectionSizeBound (mutCtx : Ix.MutCtx)
    (inputs : List (Ix.Expr × List Ix.Name))
    (before after : Ix.CompileM.ExprTableCollection) : Prop where
  refs : after.1.size ≤ before.1.size + preseedInputRefCount mutCtx inputs
  univs : after.2.1.size ≤
    before.2.1.size + preseedInputUnivCount inputs

/-- Every collected leaf payload has reached the corresponding committed
lookup map; raw collected universes are looked up by their canonical forms. -/
structure PreseedCollectionIndexed
    (refs : Array Address) (univs : Array Ixon.Univ)
    (state : Ix.CompileM.BlockState) : Prop where
  refs : ∀ addr ∈ refs,
    ∃ idx, state.refsIndex.get? addr = some idx
  univs : ∀ raw ∈ univs,
    ∃ idx, state.univsIndex.get? (Ixon.canonUniv raw) = some idx

/-- Source leaves are present in the raw collection arrays. This is the exact
collector-side property whose preservation across seen-set hits remains to be
proved. -/
inductive PreseedCollectionCovers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin : Ix.CompileM.BlockState)
    (refs : Array Address) (univs : Array Ixon.Univ) : Ix.Expr → Prop where
  | bvar {idx hash} :
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.bvar idx hash)
  | sort {level hash} :
      (∃ raw, compileUnivRef (univParamIndex blockEnv.univCtx) level =
        some raw ∧ raw ∈ univs) →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.sort level hash)
  | const {name levels hash} :
      (∀ level ∈ levels, ∃ raw,
        compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw ∧
          raw ∈ univs) →
      (blockEnv.mutCtx.get? name = none →
        ∃ addr, resolveConstAddr? compileEnv origin name = some addr ∧
          addr ∈ refs) →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.const name levels hash)
  | app {fn arg hash} :
      PreseedCollectionCovers compileEnv blockEnv origin refs univs fn →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs arg →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.app fn arg hash)
  | lam {name ty body bi hash} :
      PreseedCollectionCovers compileEnv blockEnv origin refs univs ty →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs body →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.lam name ty body bi hash)
  | all {name ty body bi hash} :
      PreseedCollectionCovers compileEnv blockEnv origin refs univs ty →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs body →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.forallE name ty body bi hash)
  | letE {name ty value body nonDep hash} :
      PreseedCollectionCovers compileEnv blockEnv origin refs univs ty →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs value →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs body →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.letE name ty value body nonDep hash)
  | lit {literal hash} :
      literalAddress literal ∈ refs →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.lit literal hash)
  | proj {typeName field value hash} :
      (∃ addr, resolveConstAddr? compileEnv origin typeName = some addr ∧
        addr ∈ refs) →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs value →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.proj typeName field value hash)
  | mdata {data inner hash} :
      PreseedCollectionCovers compileEnv blockEnv origin refs univs inner →
      PreseedCollectionCovers compileEnv blockEnv origin refs univs
        (.mdata data inner hash)

/-- A simple structural measure used only by the seen-set ghost invariant. -/
def preseedExprSize : Ix.Expr → Nat
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 1
  | .app fn arg _ => preseedExprSize fn + preseedExprSize arg + 1
  | .lam _ ty body _ _ | .forallE _ ty body _ _ =>
    preseedExprSize ty + preseedExprSize body + 1
  | .letE _ ty value body _ _ =>
    preseedExprSize ty + preseedExprSize value + preseedExprSize body + 1
  | .proj _ _ value _ => preseedExprSize value + 1
  | .mdata _ inner _ => preseedExprSize inner + 1

/-- Raw collection payloads only grow. The seen map is deliberately omitted:
coverage is monotone in the two arrays independently of traversal history. -/
structure PreseedCollectionExtends
    (before after : Ix.CompileM.ExprTableCollection) : Prop where
  refs : ∀ addr ∈ before.1, addr ∈ after.1
  univs : ∀ raw ∈ before.2.1, raw ∈ after.2.1

theorem PreseedCollectionExtends.refl
    (collection : Ix.CompileM.ExprTableCollection) :
    PreseedCollectionExtends collection collection :=
  ⟨fun _ hmem => hmem, fun _ hmem => hmem⟩

theorem PreseedCollectionExtends.trans
    {first second third : Ix.CompileM.ExprTableCollection}
    (hfirst : PreseedCollectionExtends first second)
    (hsecond : PreseedCollectionExtends second third) :
    PreseedCollectionExtends first third :=
  ⟨fun addr hmem => hsecond.refs addr (hfirst.refs addr hmem),
    fun raw hmem => hsecond.univs raw (hfirst.univs raw hmem)⟩

theorem PreseedCollectionExtends.withSeen
    (refs : Array Address) (univs : Array Ixon.Univ)
    (seen seen' : Std.HashMap (Address × Address) Unit) :
    PreseedCollectionExtends (refs, univs, seen) (refs, univs, seen') :=
  ⟨fun _ hmem => hmem, fun _ hmem => hmem⟩

theorem PreseedCollectionExtends.pushRef
    (refs : Array Address) (univs : Array Ixon.Univ)
    (seen seen' : Std.HashMap (Address × Address) Unit) (addr : Address) :
    PreseedCollectionExtends (refs, univs, seen)
      (refs.push addr, univs, seen') := by
  constructor
  · intro value hmem
    simp only [Array.mem_push]
    exact Or.inl hmem
  · intro raw hmem
    exact hmem

theorem PreseedCollectionExtends.pushUniv
    (refs : Array Address) (univs : Array Ixon.Univ)
    (seen seen' : Std.HashMap (Address × Address) Unit) (raw : Ixon.Univ) :
    PreseedCollectionExtends (refs, univs, seen)
      (refs, univs.push raw, seen') := by
  constructor
  · intro addr hmem
    exact hmem
  · intro value hmem
    simp only [Array.mem_push]
    exact Or.inl hmem

theorem PreseedCollectionCovers.mono
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {origin : Ix.CompileM.BlockState}
    {before after : Ix.CompileM.ExprTableCollection} {source : Ix.Expr}
    (hsource : PreseedCollectionCovers compileEnv blockEnv origin
      before.1 before.2.1 source)
    (hextends : PreseedCollectionExtends before after) :
    PreseedCollectionCovers compileEnv blockEnv origin
      after.1 after.2.1 source := by
  induction hsource with
  | bvar => exact .bvar
  | sort hlevel =>
    obtain ⟨raw, href, hmem⟩ := hlevel
    exact .sort ⟨raw, href, hextends.univs raw hmem⟩
  | const hlevels hresolve =>
    apply PreseedCollectionCovers.const
    · intro level hmem
      obtain ⟨raw, href, hrawMem⟩ := hlevels level hmem
      exact ⟨raw, href, hextends.univs raw hrawMem⟩
    · intro hmut
      obtain ⟨addr, haddr, haddrMem⟩ := hresolve hmut
      exact ⟨addr, haddr, hextends.refs addr haddrMem⟩
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ ihty ihbody => exact .lam ihty ihbody
  | all _ _ ihty ihbody => exact .all ihty ihbody
  | letE _ _ _ ihty ihvalue ihbody => exact .letE ihty ihvalue ihbody
  | lit hmem => exact .lit (hextends.refs _ hmem)
  | proj hresolve _ ihvalue =>
    obtain ⟨addr, haddr, hmem⟩ := hresolve
    exact .proj ⟨addr, haddr, hextends.refs addr hmem⟩ ihvalue
  | mdata _ ihinner => exact .mdata ihinner

/-- Seen-set soundness during a structural walk. Every hit is either already
covered by the accumulated arrays or represented by an active ancestor. -/
def PreseedSeenCovers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin : Ix.CompileM.BlockState)
    (ctxKey : Address) (active : List Ix.Expr)
    (collection : Ix.CompileM.ExprTableCollection) : Prop :=
  ∀ queried, OrdinaryExpr queried →
    collection.2.2.contains (queried.getHash, ctxKey) = true →
    PreseedCollectionCovers compileEnv blockEnv origin
        collection.1 collection.2.1 queried ∨
      ∃ stored ∈ active, OrdinaryExpr stored ∧ (stored == queried) = true

theorem PreseedSeenCovers.empty
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (origin : Ix.CompileM.BlockState)
    (ctxKey : Address) :
    PreseedSeenCovers compileEnv blockEnv origin ctxKey [] (#[], #[], {}) := by
  intro queried hordinary hcontains
  simp at hcontains

private theorem expr_beq_of_seenKey_beq
    (stored queried : Ix.Expr) (ctxKey : Address)
    (hkey : ((stored.getHash, ctxKey) ==
      (queried.getHash, ctxKey)) = true) :
    (stored == queried) = true := by
  have hp : (stored.getHash, ctxKey) =
      (queried.getHash, ctxKey) := eq_of_beq hkey
  have hhash : stored.getHash = queried.getHash :=
    congrArg Prod.fst hp
  change (stored.getHash == queried.getHash) = true
  rw [hhash]
  exact beq_self_eq_true _

theorem PreseedSeenCovers.insert
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {origin : Ix.CompileM.BlockState}
    {ctxKey : Address} {active : List Ix.Expr}
    {refs : Array Address} {univs : Array Ixon.Univ}
    {seen : Std.HashMap (Address × Address) Unit}
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey active
      (refs, univs, seen))
    (stored : Ix.Expr) (hstored : OrdinaryExpr stored) :
    PreseedSeenCovers compileEnv blockEnv origin ctxKey (stored :: active)
      (refs, univs, seen.insert (stored.getHash, ctxKey) ()) := by
  intro queried hqueried hcontains
  rw [Std.HashMap.contains_insert] at hcontains
  simp only [Bool.or_eq_true] at hcontains
  rcases hcontains with hkey | hcontains
  · exact Or.inr ⟨stored, by simp, hstored,
      expr_beq_of_seenKey_beq stored queried ctxKey hkey⟩
  · rcases hseen queried hqueried hcontains with hcovered |
        ⟨activeExpr, hmem, hordinary, hbeq⟩
    · exact Or.inl hcovered
    · exact Or.inr ⟨activeExpr, by simp [hmem], hordinary, hbeq⟩

theorem PreseedSeenCovers.monoArrays
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {origin : Ix.CompileM.BlockState}
    {ctxKey : Address} {active : List Ix.Expr}
    {before after : Ix.CompileM.ExprTableCollection}
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey active before)
    (hextends : PreseedCollectionExtends before after)
    (hseenMap : after.2.2 = before.2.2) :
    PreseedSeenCovers compileEnv blockEnv origin ctxKey active after := by
  intro queried hqueried hcontains
  rw [hseenMap] at hcontains
  rcases hseen queried hqueried hcontains with hcovered | hactive
  · exact Or.inl (hcovered.mono hextends)
  · exact Or.inr hactive

theorem PreseedSeenCovers.cover_of_hit
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {origin : Ix.CompileM.BlockState}
    {ctxKey : Address} {active : List Ix.Expr}
    {collection : Ix.CompileM.ExprTableCollection} {source : Ix.Expr}
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey active
      collection)
    (hfaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hsource : OrdinaryExpr source)
    (hactive : ∀ stored ∈ active,
      preseedExprSize source < preseedExprSize stored)
    (hhit : collection.2.2.contains (source.getHash, ctxKey) = true) :
    PreseedCollectionCovers compileEnv blockEnv origin
      collection.1 collection.2.1 source := by
  rcases hseen source hsource hhit with hcovered |
      ⟨stored, hmem, hstored, hbeq⟩
  · exact hcovered
  · have heq : stored = source := hfaithful hstored hbeq
    subst stored
    exact (Nat.lt_irrefl _ (hactive source hmem)).elim

theorem PreseedSeenCovers.dropHead
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {origin : Ix.CompileM.BlockState}
    {ctxKey : Address} {active : List Ix.Expr}
    {collection : Ix.CompileM.ExprTableCollection} {source : Ix.Expr}
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey
      (source :: active) collection)
    (hfaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (hsource : OrdinaryExpr source)
    (hcovered : PreseedCollectionCovers compileEnv blockEnv origin
      collection.1 collection.2.1 source) :
    PreseedSeenCovers compileEnv blockEnv origin ctxKey active collection := by
  intro queried hqueried hcontains
  rcases hseen queried hqueried hcontains with hqueryCovered |
      ⟨stored, hmem, hstored, hbeq⟩
  · exact Or.inl hqueryCovered
  · simp only [List.mem_cons] at hmem
    rcases hmem with hhead | hmem
    · subst stored
      have heq : source = queried := hfaithful hsource hbeq
      subst queried
      exact Or.inl hcovered
    · exact Or.inr ⟨stored, hmem, hstored, hbeq⟩

private theorem list_mapM_exists_of_mem
    {f : α → Option β} {values : List α}
    (h : ∀ value ∈ values, ∃ result, f value = some result) :
    ∃ results, values.mapM f = some results := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons value rest ih =>
    obtain ⟨result, hresult⟩ := h value (by simp)
    have hrest : ∀ item ∈ rest, ∃ target, f item = some target := by
      intro item hmem
      exact h item (by simp [hmem])
    obtain ⟨results, hresults⟩ := ih hrest
    exact ⟨result :: results, by simp [hresult, hresults]⟩

private theorem array_mapM_exists_of_mem
    {f : α → Option β} {values : Array α}
    (h : ∀ value ∈ values, ∃ result, f value = some result) :
    ∃ results, values.mapM f = some results := by
  have hlist : ∀ value ∈ values.toList,
      ∃ result, f value = some result := by
    intro value hmem
    exact h value (by simpa using hmem)
  obtain ⟨results, hresults⟩ := list_mapM_exists_of_mem hlist
  refine ⟨results.toArray, ?_⟩
  rw [Array.mapM_eq_mapM_toList, hresults]
  rfl

theorem PreseedCollectionCovers.compileExprRef_of_indexed
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {origin state : Ix.CompileM.BlockState}
    {refs : Array Address} {univs : Array Ixon.Univ} {source : Ix.Expr}
    (hsource : PreseedCollectionCovers compileEnv blockEnv origin refs univs
      source)
    (hindexed : PreseedCollectionIndexed refs univs state)
    (hresolution : ∀ name, resolveConstAddr? compileEnv state name =
      resolveConstAddr? compileEnv origin name) :
    ∃ target, compileExprRef (frozenRefCompileCtx compileEnv blockEnv state)
      source = some target := by
  induction hsource with
  | @bvar idx hash =>
    exact ⟨.var idx.toUInt64, rfl⟩
  | @sort level hash hlevel =>
    obtain ⟨raw, hraw, hmem⟩ := hlevel
    obtain ⟨idx, hidx⟩ := hindexed.univs raw hmem
    change state.univsIndex[Ixon.canonUniv raw]? = some idx at hidx
    refine ⟨.sort idx, ?_⟩
    simp [compileExprRef, frozenRefCompileCtx, hraw, hidx]
  | @const name levels hash hlevels hresolve =>
    have hlevelIndexes : ∀ level ∈ levels,
        ∃ idx, (frozenRefCompileCtx compileEnv blockEnv state).univIndex
          level = some idx := by
      intro level hmem
      obtain ⟨raw, hraw, hrawMem⟩ := hlevels level hmem
      obtain ⟨idx, hidx⟩ := hindexed.univs raw hrawMem
      change state.univsIndex[Ixon.canonUniv raw]? = some idx at hidx
      exact ⟨idx, by simp [frozenRefCompileCtx, hraw, hidx]⟩
    obtain ⟨indices, hindices⟩ :=
      array_mapM_exists_of_mem hlevelIndexes
    cases hmut : blockEnv.mutCtx.get? name with
    | some mutIdx =>
      refine ⟨.recur mutIdx.toUInt64 indices, ?_⟩
      rw [compileExprRef, hindices]
      simp only [frozenRefCompileCtx]
      rw [hmut]
      rfl
    | none =>
      obtain ⟨addr, haddr, haddrMem⟩ := hresolve hmut
      obtain ⟨idx, hidx⟩ := hindexed.refs addr haddrMem
      change state.refsIndex[addr]? = some idx at hidx
      have haddrState : resolveConstAddr? compileEnv state name =
          some addr := by
        rw [hresolution name]
        exact haddr
      refine ⟨.ref idx indices, ?_⟩
      rw [compileExprRef, hindices]
      simp only [frozenRefCompileCtx]
      rw [hmut]
      simp [haddrState, hidx]
  | @app fn arg hash hfn harg ihfn iharg =>
    obtain ⟨fnTarget, hfnTarget⟩ := ihfn
    obtain ⟨argTarget, hargTarget⟩ := iharg
    exact ⟨.app fnTarget argTarget,
      by simp [compileExprRef, hfnTarget, hargTarget]⟩
  | @lam name ty body bi hash hty hbody ihty ihbody =>
    obtain ⟨tyTarget, htyTarget⟩ := ihty
    obtain ⟨bodyTarget, hbodyTarget⟩ := ihbody
    exact ⟨.leanLam tyTarget bodyTarget,
      by simp [compileExprRef, htyTarget, hbodyTarget]⟩
  | @all name ty body bi hash hty hbody ihty ihbody =>
    obtain ⟨tyTarget, htyTarget⟩ := ihty
    obtain ⟨bodyTarget, hbodyTarget⟩ := ihbody
    exact ⟨.leanAll tyTarget bodyTarget,
      by simp [compileExprRef, htyTarget, hbodyTarget]⟩
  | @letE name ty value body nonDep hash hty hvalue hbody
      ihty ihvalue ihbody =>
    obtain ⟨tyTarget, htyTarget⟩ := ihty
    obtain ⟨valueTarget, hvalueTarget⟩ := ihvalue
    obtain ⟨bodyTarget, hbodyTarget⟩ := ihbody
    exact ⟨.letE nonDep tyTarget valueTarget bodyTarget,
      by simp [compileExprRef, htyTarget, hvalueTarget, hbodyTarget]⟩
  | @lit literal hash hmem =>
    obtain ⟨idx, hidx⟩ := hindexed.refs (literalAddress literal) hmem
    change state.refsIndex[literalAddress literal]? = some idx at hidx
    cases literal with
    | natVal value =>
      refine ⟨.nat idx, ?_⟩
      simp [compileExprRef, frozenRefCompileCtx]
      simpa [literalAddress] using hidx
    | strVal value =>
      refine ⟨.str idx, ?_⟩
      simp [compileExprRef, frozenRefCompileCtx]
      simpa [literalAddress] using hidx
  | @proj typeName field value hash hresolve hvalue ihvalue =>
    obtain ⟨addr, haddr, hmem⟩ := hresolve
    obtain ⟨idx, hidx⟩ := hindexed.refs addr hmem
    change state.refsIndex[addr]? = some idx at hidx
    have haddrState : resolveConstAddr? compileEnv state typeName =
        some addr := by
      rw [hresolution typeName]
      exact haddr
    obtain ⟨valueTarget, hvalueTarget⟩ := ihvalue
    have hrefIndex :
        (frozenRefCompileCtx compileEnv blockEnv state).refIndex typeName =
          some idx := by
      simp [frozenRefCompileCtx, haddrState, hidx]
    refine ⟨.prj idx field.toUInt64 valueTarget, ?_⟩
    rw [compileExprRef, hrefIndex, hvalueTarget]
    rfl
  | @mdata data inner hash hinner ihinner =>
    exact ihinner

private theorem run_lookupConstAddr_resolved
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) (addr : Address)
    (hresolve : resolveConstAddr? compileEnv state name = some addr) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.lookupConstAddr name) = .ok (addr, state) := by
  rw [Ix.CompileM.lookupConstAddr,
    run_bind compileEnv blockEnv state Ix.CompileM.getCompileEnv,
    run_getCompileEnv]
  simp only
  rw [run_bind compileEnv blockEnv state Ix.CompileM.getBlockState,
    run_getBlockState]
  simp only
  unfold resolveConstAddr? at hresolve
  cases hblock : state.blockNameToAddr.get? name with
  | some found =>
    simp only [hblock, Option.some.injEq] at hresolve
    subst found
    simp only
    rfl
  | none =>
    simp only [hblock] at hresolve
    simp only
    cases hglobal : compileEnv.nameToAddr.get? name with
    | some found =>
      simp only [hglobal, Option.some.injEq] at hresolve
      subst found
      simp only
      rfl
    | none =>
      simp only [hglobal] at hresolve
      simp only
      cases hblockAux : state.auxNameToAddr.get? name with
      | some found =>
        simp only [hblockAux, Option.some.injEq] at hresolve
        subst found
        simp only
        rfl
      | none =>
        simp only [hblockAux] at hresolve
        simp only
        change compileEnv.auxNameToAddr.get? name = some addr at hresolve
        rw [hresolve]
        rfl

/-- Compiling and appending a ready source level list preserves the collector
state frame. -/
theorem collectExprTableUnivs_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    (levels : List Ix.Level) (initial : Array Ixon.Univ)
    {state : Ix.CompileM.BlockState}
    (hlevels : ∀ level ∈ levels, levelSupport level ∧
      ∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) level = some u ∧
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv u))
    (hwire : ∀ u ∈ initial,
      Codec.Ixon.Univ.WireWF (Ixon.canonUniv u))
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTableUnivs levels initial) =
        .ok (result, state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      (∀ u ∈ result,
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv u)) ∧
      result.size = initial.size + levels.length := by
  induction levels generalizing initial state with
  | nil => exact ⟨initial, state, rfl, hstate, hwire, by simp⟩
  | cons level rest ih =>
    obtain ⟨hlevel, target, href, htargetWire⟩ :=
      hlevels level (by simp)
    obtain ⟨univState, hunivRun, hunivState, htables, hexpr,
        hcanon, harena⟩ :=
      compileUniv_run_refines compileEnv blockEnv hclosed hfaithful
        hlevel hstate.univCache href
    have hunivFrame : PreseedCollectStateWF compileEnv blockEnv levelSupport
        origin univState :=
      hstate.of_compileUniv hunivState htables hexpr hcanon harena
    have hrest : ∀ value ∈ rest, levelSupport value ∧
        ∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) value = some u ∧
          Codec.Ixon.Univ.WireWF (Ixon.canonUniv u) := by
      intro value hmem
      exact hlevels value (by simp [hmem])
    have hpushWire : ∀ value ∈ initial.push target,
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv value) := by
      intro value hmem
      simp only [Array.mem_push] at hmem
      rcases hmem with hmem | rfl
      · exact hwire value hmem
      · exact htargetWire
    obtain ⟨result, state', hrestRun, hstate', hresultWire,
        hresultSize⟩ :=
      ih (initial := initial.push target) hrest hpushWire hunivFrame
    refine ⟨result, state', ?_, hstate', hresultWire, ?_⟩
    · rw [Ix.CompileM.collectExprTableUnivs, run_bind, hunivRun]
      exact hrestRun
    · simp only [List.length_cons, Array.size_push] at hresultSize ⊢
      omega

/-- The universe-list collector preserves every initial element and includes
a reference compilation of every requested source level. -/
theorem collectExprTableUnivs_run_refines_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    (levels : List Ix.Level) (initial : Array Ixon.Univ)
    {state : Ix.CompileM.BlockState}
    (hlevels : ∀ level ∈ levels, levelSupport level ∧
      ∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) level = some u ∧
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv u))
    (hwire : ∀ u ∈ initial,
      Codec.Ixon.Univ.WireWF (Ixon.canonUniv u))
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTableUnivs levels initial) =
        .ok (result, state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      (∀ u ∈ result,
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv u)) ∧
      (∀ u ∈ initial, u ∈ result) ∧
      (∀ level ∈ levels, ∃ u,
        compileUnivRef (univParamIndex blockEnv.univCtx) level = some u ∧
          u ∈ result) := by
  induction levels generalizing initial state with
  | nil =>
    exact ⟨initial, state, rfl, hstate, hwire,
      fun _ hmem => hmem, by simp⟩
  | cons level rest ih =>
    obtain ⟨hlevel, target, href, htargetWire⟩ :=
      hlevels level (by simp)
    obtain ⟨univState, hunivRun, hunivState, htables, hexpr,
        hcanon, harena⟩ :=
      compileUniv_run_refines compileEnv blockEnv hclosed hfaithful
        hlevel hstate.univCache href
    have hunivFrame : PreseedCollectStateWF compileEnv blockEnv levelSupport
        origin univState :=
      hstate.of_compileUniv hunivState htables hexpr hcanon harena
    have hrest : ∀ value ∈ rest, levelSupport value ∧
        ∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) value = some u ∧
          Codec.Ixon.Univ.WireWF (Ixon.canonUniv u) := by
      intro value hmem
      exact hlevels value (by simp [hmem])
    have hpushWire : ∀ value ∈ initial.push target,
        Codec.Ixon.Univ.WireWF (Ixon.canonUniv value) := by
      intro value hmem
      simp only [Array.mem_push] at hmem
      rcases hmem with hmem | rfl
      · exact hwire value hmem
      · exact htargetWire
    obtain ⟨result, state', hrestRun, hstate', hresultWire,
        hinitialPush, hrestCovers⟩ :=
      ih (initial := initial.push target) hrest hpushWire hunivFrame
    refine ⟨result, state', ?_, hstate', hresultWire, ?_, ?_⟩
    · rw [Ix.CompileM.collectExprTableUnivs, run_bind, hunivRun]
      exact hrestRun
    · intro value hmem
      exact hinitialPush value (by simp [hmem])
    · intro value hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨target, href, hinitialPush target (by simp)⟩
      · exact hrestCovers value hmem

/-- The proof-visible structural collector is total on every preseed-ready
ordinary source. It may extend only the context-sensitive universe memo and
blob store; all state needed to freeze the later expression compiler remains
sound. The digest/context seen-set branch is harmless for this success/frame
property—coverage of skipped leaves is proved separately. -/
theorem collectExprTablesStructural_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    (ctxKey : Address) {source : Ix.Expr}
    (hsource : PreseedReady compileEnv blockEnv levelSupport origin source)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    {state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTablesStructural
            ctxKey blockEnv.mutCtx source acc) = .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionSizeBound blockEnv.mutCtx source acc acc' := by
  induction hsource generalizing state acc with
  | @bvar idx hash =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen :
        seen.contains ((Ix.Expr.bvar idx hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
  | @sort level hash hlevel href =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen :
        seen.contains ((Ix.Expr.sort level hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨target, href, htargetWire⟩ := href
      obtain ⟨state', hrun, huniv, htables, hexpr, hcanon, harena⟩ :=
        compileUniv_run_refines compileEnv blockEnv hclosed hfaithful
          hlevel hstate.univCache href
      let hstate' :=
        hstate.of_compileUniv huniv htables hexpr hcanon harena
      refine ⟨(refs, univs.push target,
        seen.insert ((Ix.Expr.sort level hash).getHash, ctxKey) ()),
        state', ?_, hstate',
        hcollection.pushUniv target htargetWire,
        ⟨by simp [preseedRefCount], by simp [preseedUnivCount]⟩⟩
      rw [run_bind, hrun]
      rfl
  | @const name levels hash hlevels hresolve =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen :
        seen.contains ((Ix.Expr.const name levels hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      have hlevelsList : ∀ level ∈ levels.toList, levelSupport level ∧
          ∃ u, compileUnivRef (univParamIndex blockEnv.univCtx) level =
            some u ∧ Codec.Ixon.Univ.WireWF (Ixon.canonUniv u) := by
        intro level hmem
        exact hlevels level (by simpa using hmem)
      obtain ⟨compiled, univState, hunivsRun, hunivState,
          hcompiledWire, hcompiledSize⟩ :=
        collectExprTableUnivs_run_refines compileEnv blockEnv origin
          hclosed hfaithful levels.toList univs hlevelsList
          hcollection.univs hstate
      have hcompiled : PreseedCollectionWireWF (refs, compiled, seen) :=
        ⟨hcollection.refs, hcompiledWire⟩
      cases hmut : blockEnv.mutCtx.get? name with
      | some idx =>
        refine ⟨(refs, compiled,
          seen.insert ((Ix.Expr.const name levels hash).getHash, ctxKey) ()),
          univState, ?_, hunivState, hcompiled.withSeen,
          ⟨by dsimp [preseedRefCount]; omega,
            by rw [hcompiledSize]; simp [preseedUnivCount]⟩⟩
        rw [run_bind, hunivsRun]
        simp only
        rw [hmut]
        rfl
      | none =>
        obtain ⟨addr, haddr, haddrWire⟩ := hresolve hmut
        have haddrLive :
            resolveConstAddr? compileEnv univState name = some addr := by
          rw [resolveConstAddr?_of_exprTableView_eq compileEnv
            hunivState.tables]
          exact haddr
        have hlookup := run_lookupConstAddr_resolved compileEnv blockEnv
          univState name addr haddrLive
        refine ⟨(refs.push addr, compiled,
          seen.insert ((Ix.Expr.const name levels hash).getHash, ctxKey) ()),
          univState, ?_,
          hunivState, hcompiled.pushRef addr haddrWire,
          ⟨by
            simp only [Array.size_push]
            change refs.size + 1 ≤ refs.size +
              (match blockEnv.mutCtx.get? name with
              | some _ => 0
              | none => 1)
            rw [hmut]
            exact Nat.le_refl _
          , by rw [hcompiledSize]; simp [preseedUnivCount]⟩⟩
        rw [run_bind, hunivsRun]
        simp only
        rw [hmut]
        simp only [Option.isNone, if_true]
        rw [run_bind, hlookup]
        rfl
  | @app fn arg hash hfn harg ihfn iharg =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen :
        seen.contains ((Ix.Expr.app fn arg hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨fnAcc, fnState, hfnRun, hfnState, hfnCollection,
          hfnSize⟩ :=
        ihfn (refs, univs,
          seen.insert ((Ix.Expr.app fn arg hash).getHash, ctxKey) ())
          hcollection.withSeen hstate
      obtain ⟨argAcc, argState, hargRun, hargState, hargCollection,
          hargSize⟩ :=
        iharg fnAcc hfnCollection hfnState
      exact ⟨argAcc, argState, by rw [run_bind, hfnRun]; exact hargRun,
        hargState, hargCollection,
        ⟨by
          have hfnRef := hfnSize.refs
          have hargRef := hargSize.refs
          dsimp [preseedRefCount] at hfnRef hargRef ⊢
          omega,
          by
          have hfnUniv := hfnSize.univs
          have hargUniv := hargSize.univs
          dsimp [preseedUnivCount] at hfnUniv hargUniv ⊢
          omega⟩⟩
  | @lam name ty body bi hash hty hbody ihty ihbody =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen : seen.contains
      ((Ix.Expr.lam name ty body bi hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨tyAcc, tyState, htyRun, htyState, htyCollection,
          htySize⟩ :=
        ihty (refs, univs, seen.insert
          ((Ix.Expr.lam name ty body bi hash).getHash, ctxKey) ())
          hcollection.withSeen hstate
      obtain ⟨bodyAcc, bodyState, hbodyRun, hbodyState, hbodyCollection,
          hbodySize⟩ :=
        ihbody tyAcc htyCollection htyState
      exact ⟨bodyAcc, bodyState, by rw [run_bind, htyRun]; exact hbodyRun,
        hbodyState, hbodyCollection,
        ⟨by
          have htyRef := htySize.refs
          have hbodyRef := hbodySize.refs
          dsimp [preseedRefCount] at htyRef hbodyRef ⊢
          omega,
          by
          have htyUniv := htySize.univs
          have hbodyUniv := hbodySize.univs
          dsimp [preseedUnivCount] at htyUniv hbodyUniv ⊢
          omega⟩⟩
  | @all name ty body bi hash hty hbody ihty ihbody =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen : seen.contains
      ((Ix.Expr.forallE name ty body bi hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨tyAcc, tyState, htyRun, htyState, htyCollection,
          htySize⟩ :=
        ihty (refs, univs, seen.insert
          ((Ix.Expr.forallE name ty body bi hash).getHash, ctxKey) ())
          hcollection.withSeen hstate
      obtain ⟨bodyAcc, bodyState, hbodyRun, hbodyState, hbodyCollection,
          hbodySize⟩ :=
        ihbody tyAcc htyCollection htyState
      exact ⟨bodyAcc, bodyState, by rw [run_bind, htyRun]; exact hbodyRun,
        hbodyState, hbodyCollection,
        ⟨by
          have htyRef := htySize.refs
          have hbodyRef := hbodySize.refs
          dsimp [preseedRefCount] at htyRef hbodyRef ⊢
          omega,
          by
          have htyUniv := htySize.univs
          have hbodyUniv := hbodySize.univs
          dsimp [preseedUnivCount] at htyUniv hbodyUniv ⊢
          omega⟩⟩
  | @letE name ty val body nonDep hash hty hval hbody ihty ihval ihbody =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen : seen.contains
      ((Ix.Expr.letE name ty val body nonDep hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨tyAcc, tyState, htyRun, htyState, htyCollection,
          htySize⟩ :=
        ihty (refs, univs, seen.insert
          ((Ix.Expr.letE name ty val body nonDep hash).getHash, ctxKey) ())
          hcollection.withSeen hstate
      obtain ⟨valAcc, valState, hvalRun, hvalState, hvalCollection,
          hvalSize⟩ :=
        ihval tyAcc htyCollection htyState
      obtain ⟨bodyAcc, bodyState, hbodyRun, hbodyState,
          hbodyCollection, hbodySize⟩ :=
        ihbody valAcc hvalCollection hvalState
      refine ⟨bodyAcc, bodyState, ?_, hbodyState, hbodyCollection,
        ⟨?_, ?_⟩⟩
      rw [run_bind, htyRun]
      simp only
      rw [run_bind, hvalRun]
      exact hbodyRun
      · have htyRef := htySize.refs
        have hvalRef := hvalSize.refs
        have hbodyRef := hbodySize.refs
        dsimp [preseedRefCount] at htyRef hvalRef hbodyRef ⊢
        omega
      · have htyUniv := htySize.univs
        have hvalUniv := hvalSize.univs
        have hbodyUniv := hbodySize.univs
        dsimp [preseedUnivCount] at htyUniv hvalUniv hbodyUniv ⊢
        omega
  | @lit literal hash =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen :
      seen.contains ((Ix.Expr.lit literal hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      cases literal with
      | natVal n =>
        let bytes := ByteArray.mk (Nat.toBytesLE n)
        let addr := Address.blake3 bytes
        let state' := preseedBlobState state addr bytes
        refine ⟨(refs.push addr, univs,
          seen.insert ((Ix.Expr.lit (.natVal n) hash).getHash, ctxKey) ()),
          state', ?_, ?_,
          hcollection.pushRef addr (addressBlake3_wire bytes),
          ⟨by simp [preseedRefCount], by simp [preseedUnivCount]⟩⟩
        · rfl
        · exact hstate.blob addr bytes
      | strVal s =>
        let bytes := s.toUTF8
        let addr := Address.blake3 bytes
        let state' := preseedBlobState state addr bytes
        refine ⟨(refs.push addr, univs,
          seen.insert ((Ix.Expr.lit (.strVal s) hash).getHash, ctxKey) ()),
          state', ?_, ?_,
          hcollection.pushRef addr (addressBlake3_wire bytes),
          ⟨by simp [preseedRefCount], by simp [preseedUnivCount]⟩⟩
        · rfl
        · exact hstate.blob addr bytes
  | @proj typeName field val hash hresolve hval ihval =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen : seen.contains
      ((Ix.Expr.proj typeName field val hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨addr, haddr, haddrWire⟩ := hresolve
      have haddrLive : resolveConstAddr? compileEnv state typeName =
          some addr := by
        rw [resolveConstAddr?_of_exprTableView_eq compileEnv hstate.tables]
        exact haddr
      have hlookup := run_lookupConstAddr_resolved compileEnv blockEnv state
        typeName addr haddrLive
      obtain ⟨valAcc, valState, hvalRun, hvalState, hvalCollection,
          hvalSize⟩ :=
        ihval (refs.push addr, univs,
          seen.insert ((Ix.Expr.proj typeName field val hash).getHash,
            ctxKey) ()) (hcollection.pushRef addr haddrWire) hstate
      refine ⟨valAcc, valState, ?_, hvalState, hvalCollection,
        ⟨?_, ?_⟩⟩
      · rw [run_bind, hlookup]
        exact hvalRun
      · have hvalRef := hvalSize.refs
        simp only [Array.size_push] at hvalRef
        dsimp [preseedRefCount] at hvalRef ⊢
        omega
      · have hvalUniv := hvalSize.univs
        dsimp [preseedUnivCount] at hvalUniv ⊢
        omega
  | @mdata data inner hash hinner ihinner =>
    rcases acc with ⟨refs, univs, seen⟩
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hseen : seen.contains
      ((Ix.Expr.mdata data inner hash).getHash, ctxKey) = true
    · rw [if_pos hseen]
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        PreseedCollectionSizeBound.same ..⟩
    · rw [if_neg hseen]
      obtain ⟨innerAcc, innerState, hinnerRun, hinnerState,
          hinnerCollection, hinnerSize⟩ := ihinner
        (refs, univs,
          seen.insert ((Ix.Expr.mdata data inner hash).getHash, ctxKey) ())
        hcollection.withSeen hstate
      refine ⟨innerAcc, innerState, hinnerRun, hinnerState,
        hinnerCollection, ?_⟩
      exact ⟨by simpa [preseedRefCount] using hinnerSize.refs,
        by simpa [preseedUnivCount] using hinnerSize.univs⟩

private theorem preseedActive_of_child
    {child parent : Ix.Expr} {active : List Ix.Expr}
    (hchild : preseedExprSize child < preseedExprSize parent)
    (hactive : ∀ stored ∈ active,
      preseedExprSize parent < preseedExprSize stored) :
    ∀ stored ∈ parent :: active,
      preseedExprSize child < preseedExprSize stored := by
  intro stored hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact hchild
  · exact Nat.lt_trans hchild (hactive stored hmem)

/-- Collision-disciplined semantic refinement of the structural collector.
Alongside the executable state frame, it proves array growth, source coverage,
and preservation of the active-ancestor seen-set invariant. -/
theorem collectExprTablesStructural_run_ready_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (ctxKey : Address) {source : Ix.Expr}
    (hsource : PreseedReady compileEnv blockEnv levelSupport origin source)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    (active : List Ix.Expr)
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey active acc)
    (hactive : ∀ stored ∈ active,
      preseedExprSize source < preseedExprSize stored)
    {state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTablesStructural
            ctxKey blockEnv.mutCtx source acc) = .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionExtends acc acc' ∧
      PreseedCollectionCovers compileEnv blockEnv origin
        acc'.1 acc'.2.1 source ∧
      PreseedSeenCovers compileEnv blockEnv origin ctxKey active acc' := by
  induction hsource generalizing state acc active with
  | @bvar idx hash =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.bvar idx hash
    have hordinary : OrdinaryExpr source := .bvar
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      have hinsert := hseen.insert source hordinary
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          refs univs source := .bvar
      exact ⟨_, state, rfl, hstate, hcollection.withSeen,
        .withSeen .., hcovered,
        hinsert.dropHead hexprFaithful hordinary hcovered⟩
  | @sort level hash hlevel href =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.sort level hash
    have hordinary : OrdinaryExpr source := .sort
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      obtain ⟨target, href, htargetWire⟩ := href
      obtain ⟨state', hrun, huniv, htables, hexpr, hcanon, harena⟩ :=
        compileUniv_run_refines compileEnv blockEnv hclosed hlevelFaithful
          hlevel hstate.univCache href
      have hstate' : PreseedCollectStateWF compileEnv blockEnv levelSupport
          origin state' :=
        hstate.of_compileUniv huniv htables hexpr hcanon harena
      let seen' := seen.insert (source.getHash, ctxKey) ()
      let acc' : Ix.CompileM.ExprTableCollection :=
        (refs, univs.push target, seen')
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) acc' := .pushUniv ..
      have hinsert := hseen.insert source hordinary
      have hinsertExt : PreseedCollectionExtends
          (refs, univs, seen') acc' := .pushUniv ..
      have hseen' := hinsert.monoArrays hinsertExt rfl
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          acc'.1 acc'.2.1 source :=
        .sort ⟨target, href, by simp [acc']⟩
      refine ⟨acc', state', ?_, hstate',
        hcollection.pushUniv target htargetWire, hextends, hcovered,
        hseen'.dropHead hexprFaithful hordinary hcovered⟩
      rw [run_bind, hrun]
      rfl
  | @const name levels hash hlevels hresolve =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.const name levels hash
    have hordinary : OrdinaryExpr source := .const
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      have hlevelsList : ∀ level ∈ levels.toList,
          levelSupport level ∧ ∃ u,
            compileUnivRef (univParamIndex blockEnv.univCtx) level = some u ∧
              Codec.Ixon.Univ.WireWF (Ixon.canonUniv u) := by
        intro level hmem
        exact hlevels level (by simpa using hmem)
      obtain ⟨compiled, univState, hunivsRun, hunivState,
          hcompiledWire, hinitial, hcompiledCovers⟩ :=
        collectExprTableUnivs_run_refines_covers compileEnv blockEnv origin
          hclosed hlevelFaithful levels.toList univs hlevelsList
          hcollection.univs hstate
      let seen' := seen.insert (source.getHash, ctxKey) ()
      have hinsert := hseen.insert source hordinary
      have hcompiledExt : PreseedCollectionExtends
          (refs, univs, seen') (refs, compiled, seen') :=
        ⟨fun _ hmem => hmem, hinitial⟩
      have hseenCompiled := hinsert.monoArrays hcompiledExt rfl
      have hlevelsCovered : ∀ level ∈ levels, ∃ raw,
          compileUnivRef (univParamIndex blockEnv.univCtx) level = some raw ∧
            raw ∈ compiled := by
        intro level hmem
        exact hcompiledCovers level (by simpa using hmem)
      have hcompiledCollection : PreseedCollectionWireWF
          (refs, compiled, seen') :=
        ⟨hcollection.refs, hcompiledWire⟩
      cases hmut : blockEnv.mutCtx.get? name with
      | some idx =>
        have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
            refs compiled source := by
          apply PreseedCollectionCovers.const hlevelsCovered
          intro hnone
          rw [hmut] at hnone
          contradiction
        have hextends : PreseedCollectionExtends
            (refs, univs, seen) (refs, compiled, seen') :=
          ⟨fun _ hmem => hmem, hinitial⟩
        refine ⟨_, univState, ?_, hunivState, hcompiledCollection,
          hextends, hcovered,
          hseenCompiled.dropHead hexprFaithful hordinary hcovered⟩
        rw [run_bind, hunivsRun]
        simp only
        rw [hmut]
        rfl
      | none =>
        obtain ⟨addr, haddr, haddrWire⟩ := hresolve hmut
        have haddrLive : resolveConstAddr? compileEnv univState name =
            some addr := by
          rw [resolveConstAddr?_of_exprTableView_eq compileEnv
            hunivState.tables]
          exact haddr
        have hlookup := run_lookupConstAddr_resolved compileEnv blockEnv
          univState name addr haddrLive
        let acc' : Ix.CompileM.ExprTableCollection :=
          (refs.push addr, compiled, seen')
        have hpushExt : PreseedCollectionExtends
            (refs, compiled, seen') acc' := .pushRef ..
        have hseen' := hseenCompiled.monoArrays hpushExt rfl
        have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
            acc'.1 acc'.2.1 source := by
          apply PreseedCollectionCovers.const hlevelsCovered
          intro _
          exact ⟨addr, haddr, by simp [acc']⟩
        have hextends : PreseedCollectionExtends
            (refs, univs, seen) acc' :=
          (show PreseedCollectionExtends (refs, univs, seen)
              (refs, compiled, seen') from
            ⟨fun _ hmem => hmem, hinitial⟩).trans hpushExt
        refine ⟨acc', univState, ?_, hunivState,
          hcompiledCollection.pushRef addr haddrWire, hextends, hcovered,
          hseen'.dropHead hexprFaithful hordinary hcovered⟩
        rw [run_bind, hunivsRun]
        simp only
        rw [hmut]
        simp only [Option.isNone, if_true]
        rw [run_bind, hlookup]
        rfl
  | @app fn arg hash hfn harg ihfn iharg =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.app fn arg hash
    have hordinary : OrdinaryExpr source :=
      .app hfn.supported.ordinary harg.supported.ordinary
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      let inserted : Ix.CompileM.ExprTableCollection :=
        (refs, univs, seen.insert (source.getHash, ctxKey) ())
      have hinsert := hseen.insert source hordinary
      have hfnLt : preseedExprSize fn < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      have hargLt : preseedExprSize arg < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      obtain ⟨fnAcc, fnState, hfnRun, hfnState, hfnCollection,
          hfnExt, hfnCover, hfnSeen⟩ :=
        ihfn (acc := inserted) hcollection.withSeen
          (active := source :: active) hinsert
          (preseedActive_of_child hfnLt hactive) hstate
      obtain ⟨argAcc, argState, hargRun, hargState, hargCollection,
          hargExt, hargCover, hargSeen⟩ :=
        iharg (acc := fnAcc) hfnCollection
          (active := source :: active) hfnSeen
          (preseedActive_of_child hargLt hactive) hfnState
      have hfnCover' := hfnCover.mono hargExt
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          argAcc.1 argAcc.2.1 source := .app hfnCover' hargCover
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) argAcc :=
        (PreseedCollectionExtends.withSeen ..).trans
          (hfnExt.trans hargExt)
      exact ⟨argAcc, argState,
        by rw [run_bind, hfnRun]; exact hargRun,
        hargState, hargCollection, hextends, hcovered,
        hargSeen.dropHead hexprFaithful hordinary hcovered⟩
  | @lam name ty body bi hash hty hbody ihty ihbody =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.lam name ty body bi hash
    have hordinary : OrdinaryExpr source :=
      .lam hty.supported.ordinary hbody.supported.ordinary
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      let inserted : Ix.CompileM.ExprTableCollection :=
        (refs, univs, seen.insert (source.getHash, ctxKey) ())
      have hinsert := hseen.insert source hordinary
      have htyLt : preseedExprSize ty < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      have hbodyLt : preseedExprSize body < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      obtain ⟨tyAcc, tyState, htyRun, htyState, htyCollection,
          htyExt, htyCover, htySeen⟩ :=
        ihty (acc := inserted) hcollection.withSeen
          (active := source :: active) hinsert
          (preseedActive_of_child htyLt hactive) hstate
      obtain ⟨bodyAcc, bodyState, hbodyRun, hbodyState, hbodyCollection,
          hbodyExt, hbodyCover, hbodySeen⟩ :=
        ihbody (acc := tyAcc) htyCollection
          (active := source :: active) htySeen
          (preseedActive_of_child hbodyLt hactive) htyState
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          bodyAcc.1 bodyAcc.2.1 source :=
        .lam (htyCover.mono hbodyExt) hbodyCover
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) bodyAcc :=
        (PreseedCollectionExtends.withSeen ..).trans
          (htyExt.trans hbodyExt)
      exact ⟨bodyAcc, bodyState,
        by rw [run_bind, htyRun]; exact hbodyRun,
        hbodyState, hbodyCollection, hextends, hcovered,
        hbodySeen.dropHead hexprFaithful hordinary hcovered⟩
  | @all name ty body bi hash hty hbody ihty ihbody =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.forallE name ty body bi hash
    have hordinary : OrdinaryExpr source :=
      .all hty.supported.ordinary hbody.supported.ordinary
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      let inserted : Ix.CompileM.ExprTableCollection :=
        (refs, univs, seen.insert (source.getHash, ctxKey) ())
      have hinsert := hseen.insert source hordinary
      have htyLt : preseedExprSize ty < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      have hbodyLt : preseedExprSize body < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      obtain ⟨tyAcc, tyState, htyRun, htyState, htyCollection,
          htyExt, htyCover, htySeen⟩ :=
        ihty (acc := inserted) hcollection.withSeen
          (active := source :: active) hinsert
          (preseedActive_of_child htyLt hactive) hstate
      obtain ⟨bodyAcc, bodyState, hbodyRun, hbodyState, hbodyCollection,
          hbodyExt, hbodyCover, hbodySeen⟩ :=
        ihbody (acc := tyAcc) htyCollection
          (active := source :: active) htySeen
          (preseedActive_of_child hbodyLt hactive) htyState
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          bodyAcc.1 bodyAcc.2.1 source :=
        .all (htyCover.mono hbodyExt) hbodyCover
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) bodyAcc :=
        (PreseedCollectionExtends.withSeen ..).trans
          (htyExt.trans hbodyExt)
      exact ⟨bodyAcc, bodyState,
        by rw [run_bind, htyRun]; exact hbodyRun,
        hbodyState, hbodyCollection, hextends, hcovered,
        hbodySeen.dropHead hexprFaithful hordinary hcovered⟩
  | @letE name ty value body nonDep hash hty hvalue hbody
      ihty ihvalue ihbody =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.letE name ty value body nonDep hash
    have hordinary : OrdinaryExpr source :=
      .letE hty.supported.ordinary hvalue.supported.ordinary
        hbody.supported.ordinary
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      let inserted : Ix.CompileM.ExprTableCollection :=
        (refs, univs, seen.insert (source.getHash, ctxKey) ())
      have hinsert := hseen.insert source hordinary
      have htyLt : preseedExprSize ty < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      have hvalueLt : preseedExprSize value < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      have hbodyLt : preseedExprSize body < preseedExprSize source := by
        simp [source, preseedExprSize]
        omega
      obtain ⟨tyAcc, tyState, htyRun, htyState, htyCollection,
          htyExt, htyCover, htySeen⟩ :=
        ihty (acc := inserted) hcollection.withSeen
          (active := source :: active) hinsert
          (preseedActive_of_child htyLt hactive) hstate
      obtain ⟨valueAcc, valueState, hvalueRun, hvalueState,
          hvalueCollection, hvalueExt, hvalueCover, hvalueSeen⟩ :=
        ihvalue (acc := tyAcc) htyCollection
          (active := source :: active) htySeen
          (preseedActive_of_child hvalueLt hactive) htyState
      obtain ⟨bodyAcc, bodyState, hbodyRun, hbodyState, hbodyCollection,
          hbodyExt, hbodyCover, hbodySeen⟩ :=
        ihbody (acc := valueAcc) hvalueCollection
          (active := source :: active) hvalueSeen
          (preseedActive_of_child hbodyLt hactive) hvalueState
      have htyCover' := (htyCover.mono hvalueExt).mono hbodyExt
      have hvalueCover' := hvalueCover.mono hbodyExt
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          bodyAcc.1 bodyAcc.2.1 source :=
        .letE htyCover' hvalueCover' hbodyCover
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) bodyAcc :=
        (PreseedCollectionExtends.withSeen ..).trans
          ((htyExt.trans hvalueExt).trans hbodyExt)
      refine ⟨bodyAcc, bodyState, ?_, hbodyState, hbodyCollection,
        hextends, hcovered,
        hbodySeen.dropHead hexprFaithful hordinary hcovered⟩
      rw [run_bind, htyRun]
      simp only
      rw [run_bind, hvalueRun]
      exact hbodyRun
  | @lit literal hash =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.lit literal hash
    have hordinary : OrdinaryExpr source := .lit
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      have hinsert := hseen.insert source hordinary
      cases literal with
      | natVal n =>
        let bytes := ByteArray.mk (Nat.toBytesLE n)
        let addr := Address.blake3 bytes
        let seen' := seen.insert (source.getHash, ctxKey) ()
        let acc' : Ix.CompileM.ExprTableCollection :=
          (refs.push addr, univs, seen')
        let state' := preseedBlobState state addr bytes
        have hinsertExt : PreseedCollectionExtends
            (refs, univs, seen') acc' := .pushRef ..
        have hseen' := hinsert.monoArrays hinsertExt rfl
        have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
            acc'.1 acc'.2.1 source :=
          .lit (by simp [acc', literalAddress, addr, bytes])
        exact ⟨acc', state', rfl, hstate.blob addr bytes,
          hcollection.pushRef addr (addressBlake3_wire bytes),
          .pushRef .., hcovered,
          hseen'.dropHead hexprFaithful hordinary hcovered⟩
      | strVal s =>
        let bytes := s.toUTF8
        let addr := Address.blake3 bytes
        let seen' := seen.insert (source.getHash, ctxKey) ()
        let acc' : Ix.CompileM.ExprTableCollection :=
          (refs.push addr, univs, seen')
        let state' := preseedBlobState state addr bytes
        have hinsertExt : PreseedCollectionExtends
            (refs, univs, seen') acc' := .pushRef ..
        have hseen' := hinsert.monoArrays hinsertExt rfl
        have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
            acc'.1 acc'.2.1 source :=
          .lit (by simp [acc', literalAddress, addr, bytes])
        exact ⟨acc', state', rfl, hstate.blob addr bytes,
          hcollection.pushRef addr (addressBlake3_wire bytes),
          .pushRef .., hcovered,
          hseen'.dropHead hexprFaithful hordinary hcovered⟩
  | @proj typeName field value hash hresolve hvalue ihvalue =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.proj typeName field value hash
    have hordinary : OrdinaryExpr source := .proj hvalue.supported.ordinary
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      obtain ⟨addr, haddr, haddrWire⟩ := hresolve
      have haddrLive : resolveConstAddr? compileEnv state typeName =
          some addr := by
        rw [resolveConstAddr?_of_exprTableView_eq compileEnv hstate.tables]
        exact haddr
      have hlookup := run_lookupConstAddr_resolved compileEnv blockEnv state
        typeName addr haddrLive
      let seen' := seen.insert (source.getHash, ctxKey) ()
      let pushed : Ix.CompileM.ExprTableCollection :=
        (refs.push addr, univs, seen')
      have hinsert := hseen.insert source hordinary
      have hinsertExt : PreseedCollectionExtends
          (refs, univs, seen') pushed := .pushRef ..
      have hseenPushed := hinsert.monoArrays hinsertExt rfl
      have hvalueLt : preseedExprSize value < preseedExprSize source := by
        simp [source, preseedExprSize]
      obtain ⟨valueAcc, valueState, hvalueRun, hvalueState,
          hvalueCollection, hvalueExt, hvalueCover, hvalueSeen⟩ :=
        ihvalue (acc := pushed) (hcollection.pushRef addr haddrWire)
          (active := source :: active) hseenPushed
          (preseedActive_of_child hvalueLt hactive) hstate
      have haddrMem : addr ∈ valueAcc.1 :=
        hvalueExt.refs addr (by simp [pushed])
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          valueAcc.1 valueAcc.2.1 source :=
        .proj ⟨addr, haddr, haddrMem⟩ hvalueCover
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) valueAcc :=
        (PreseedCollectionExtends.pushRef refs univs seen seen' addr).trans
          hvalueExt
      refine ⟨valueAcc, valueState, ?_, hvalueState, hvalueCollection,
        hextends, hcovered,
        hvalueSeen.dropHead hexprFaithful hordinary hcovered⟩
      rw [run_bind, hlookup]
      exact hvalueRun
  | @mdata data inner hash hinner ihinner =>
    rcases acc with ⟨refs, univs, seen⟩
    let source := Ix.Expr.mdata data inner hash
    have hordinary : OrdinaryExpr source := .mdata hinner.supported.ordinary
    rw [Ix.CompileM.collectExprTablesStructural]
    by_cases hhit : seen.contains (source.getHash, ctxKey) = true
    · rw [if_pos hhit]
      have hcovered := hseen.cover_of_hit hexprFaithful hordinary hactive hhit
      exact ⟨_, state, rfl, hstate, hcollection,
        .refl _, hcovered, hseen⟩
    · rw [if_neg hhit]
      let inserted : Ix.CompileM.ExprTableCollection :=
        (refs, univs, seen.insert (source.getHash, ctxKey) ())
      have hinsert := hseen.insert source hordinary
      have hinnerLt : preseedExprSize inner < preseedExprSize source := by
        simp [source, preseedExprSize]
      obtain ⟨innerAcc, innerState, hinnerRun, hinnerState,
          hinnerCollection, hinnerExt, hinnerCover, hinnerSeen⟩ :=
        ihinner (acc := inserted) hcollection.withSeen
          (active := source :: active) hinsert
          (preseedActive_of_child hinnerLt hactive) hstate
      have hcovered : PreseedCollectionCovers compileEnv blockEnv origin
          innerAcc.1 innerAcc.2.1 source := .mdata hinnerCover
      have hextends : PreseedCollectionExtends
          (refs, univs, seen) innerAcc :=
        (PreseedCollectionExtends.withSeen ..).trans hinnerExt
      exact ⟨innerAcc, innerState, hinnerRun, hinnerState,
        hinnerCollection, hextends, hcovered,
        hinnerSeen.dropHead hexprFaithful hordinary hcovered⟩

/-- Production wrapper for the collision-disciplined collector refinement. -/
theorem collectExprTables_run_ready_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (ctxKey : Address) {source : Ix.Expr}
    (hsource : PreseedReady compileEnv blockEnv levelSupport origin source)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    (active : List Ix.Expr)
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey active acc)
    (hactive : ∀ stored ∈ active,
      preseedExprSize source < preseedExprSize stored)
    {state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTables source ctxKey acc) =
        .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionExtends acc acc' ∧
      PreseedCollectionCovers compileEnv blockEnv origin
        acc'.1 acc'.2.1 source ∧
      PreseedSeenCovers compileEnv blockEnv origin ctxKey active acc' := by
  obtain ⟨acc', state', hrun, hstate', hcollection', hextends, hcovered,
      hseen'⟩ :=
    collectExprTablesStructural_run_ready_covers compileEnv blockEnv origin
      hclosed hlevelFaithful hexprFaithful ctxKey hsource acc hcollection
      active hseen hactive hstate
  refine ⟨acc', state', ?_, hstate', hcollection', hextends, hcovered,
    hseen'⟩
  rw [Ix.CompileM.collectExprTables, run_bind, run_getBlockEnv]
  exact hrun

/-- Public collector wrapper: reading the mutual context is pure, so the
structural success/frame theorem applies unchanged to the production entry
point seen by `collectPreseedExprs`. -/
theorem collectExprTables_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    (ctxKey : Address) {source : Ix.Expr}
    (hsource : PreseedReady compileEnv blockEnv levelSupport origin source)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    {state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTables source ctxKey acc) =
        .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionSizeBound blockEnv.mutCtx source acc acc' := by
  obtain ⟨acc', state', hrun, hstate', hcollection', hsize'⟩ :=
    collectExprTablesStructural_run_ready compileEnv blockEnv origin
      hclosed hfaithful ctxKey hsource acc hcollection hstate
  refine ⟨acc', state', ?_, hstate', hcollection', hsize'⟩
  rw [Ix.CompileM.collectExprTables, run_bind, run_getBlockEnv]
  exact hrun

/-- Combined executable, coverage, growth, and structural-size refinement.
The two independently proved runs are deterministic, so their poststates and
collections coincide. -/
theorem collectExprTables_run_ready_covers_size
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (ctxKey : Address) {source : Ix.Expr}
    (hsource : PreseedReady compileEnv blockEnv levelSupport origin source)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    (active : List Ix.Expr)
    (hseen : PreseedSeenCovers compileEnv blockEnv origin ctxKey active acc)
    (hactive : ∀ stored ∈ active,
      preseedExprSize source < preseedExprSize stored)
    {state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectExprTables source ctxKey acc) =
        .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv blockEnv levelSupport origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionExtends acc acc' ∧
      PreseedCollectionCovers compileEnv blockEnv origin
        acc'.1 acc'.2.1 source ∧
      PreseedSeenCovers compileEnv blockEnv origin ctxKey active acc' ∧
      PreseedCollectionSizeBound blockEnv.mutCtx source acc acc' := by
  obtain ⟨acc', state', hrun, hstate', hcollection', hextends, hcovered,
      hseen'⟩ :=
    collectExprTables_run_ready_covers compileEnv blockEnv origin hclosed
      hlevelFaithful hexprFaithful ctxKey hsource acc hcollection active
      hseen hactive hstate
  obtain ⟨sizedAcc, sizedState, hsizedRun, hsizedState, hsizedCollection,
      hsize⟩ :=
    collectExprTables_run_ready compileEnv blockEnv origin hclosed
      hlevelFaithful ctxKey hsource acc hcollection hstate
  rw [hrun] at hsizedRun
  cases hsizedRun
  exact ⟨acc', state', hrun, hstate', hcollection', hextends, hcovered,
    hseen', hsize⟩

/-- Reader/state pair installed by production `withUnivCtx` for one preseed
root. -/
def preseedContextBlockEnv (blockEnv : Ix.CompileM.BlockEnv)
    (params : List Ix.Name) : Ix.CompileM.BlockEnv :=
  { blockEnv with univCtx := params }

def preseedContextStartState (state : Ix.CompileM.BlockState) :
    Ix.CompileM.BlockState :=
  { state with univCache := {} }

theorem withUnivCtx_run_eq
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (params : List Ix.Name) (action : Ix.CompileM.CompileM α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.withUnivCtx params action) =
      Ix.CompileM.CompileM.run compileEnv
        (preseedContextBlockEnv blockEnv params)
        (preseedContextStartState state) action := by
  rfl

/-- A sound context-free canonical memo plus the cache reset performed by
`withUnivCtx` initializes the collector frame for a singleton root. -/
theorem preseedContextStartState_collectWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (params : List Ix.Name)
    (levelSupport : Ix.Level → Prop) (state : Ix.CompileM.BlockState)
    (hcanon : CanonUnivCacheWF state) :
    PreseedCollectStateWF compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) (preseedContextStartState state) := by
  apply PreseedCollectStateWF.refl
  · apply UnivCacheWF.of_cache_eq
      (UnivCacheWF.empty
        (univParamIndex
          (preseedContextBlockEnv blockEnv params).univCtx)
        levelSupport)
    rfl
  · exact hcanon.of_cache_eq rfl

/-- Resetting the context-sensitive universe memo between roots preserves the
collector frame relative to the original preseed start state. -/
theorem PreseedCollectStateWF.preseedContextStartState
    {compileEnv : Ix.CompileM.CompileEnv}
    {blockEnv : Ix.CompileM.BlockEnv} {levelSupport : Ix.Level → Prop}
    {origin state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectStateWF compileEnv blockEnv levelSupport
      origin state) :
    PreseedCollectStateWF compileEnv blockEnv levelSupport origin
      (preseedContextStartState state) := by
  refine
    { tables := ?_
      exprCache := ?_
      univCache := ?_
      canonUnivCache := ?_
      arena := ?_ }
  · exact hstate.tables
  · exact hstate.exprCache
  · apply UnivCacheWF.of_cache_eq
      (UnivCacheWF.empty (univParamIndex blockEnv.univCtx) levelSupport)
    rfl
  · exact hstate.canonUnivCache.of_cache_eq rfl
  · exact hstate.arena

/-- A context-independent collector frame can initialize the next root under
arbitrary universe parameters because production clears the context-sensitive
universe memo before every root. -/
theorem PreseedCollectFrameWF.preseedContextStartState_collectWF
    {origin state : Ix.CompileM.BlockState}
    (hstate : PreseedCollectFrameWF origin state)
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (params : List Ix.Name)
    (levelSupport : Ix.Level → Prop) :
    PreseedCollectStateWF compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport origin
      (preseedContextStartState state) := by
  refine {
    tables := hstate.tables
    exprCache := hstate.exprCache
    univCache := ?_
    canonUnivCache := hstate.canonUnivCache.of_cache_eq rfl
    arena := hstate.arena }
  apply UnivCacheWF.of_cache_eq
    (UnivCacheWF.empty
      (univParamIndex (preseedContextBlockEnv blockEnv params).univCtx)
      levelSupport)
  rfl

/-- Collision discipline for the shared `(expr hash, context hash)` seen set
along one heterogeneous production traversal. The head condition says any
existing hit is already covered in that root's exact universe context; the
tail condition advances this invariant through the actual head transition.
This isolates the sole cross-context digest assumption from source readiness. -/
def HeterogeneousPreseedSeenSafe
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) :
    List (Ix.Expr × List Ix.Name) →
      Ix.CompileM.ExprTableCollection → Ix.CompileM.BlockState → Prop
  | [], _, _ => True
  | (source, params) :: rest, acc, state =>
    PreseedSeenCovers compileEnv
      (preseedContextBlockEnv blockEnv params) origin
      (Ix.CompileM.univParamsKey params) [] acc ∧
    ∀ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.withUnivCtx params
            (Ix.CompileM.collectExprTables source
              (Ix.CompileM.univParamsKey params) acc)) =
        .ok (acc', state') →
      HeterogeneousPreseedSeenSafe compileEnv blockEnv origin rest acc'
        state'

/-- A uniform universe-parameter context is a constructive sufficient
condition for the heterogeneous collector's shared seen-set discipline.  The
collector may still receive its roots through the heterogeneous production
interface, but every root uses the same context key and the ordinary
expression-key faithfulness premise closes all digest hits. -/
private theorem heterogeneousPreseedSeenSafe_of_uniform_aux
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inputs : List (Ix.Expr × List Ix.Name))
    (hparams : ∀ input ∈ inputs, input.2 = params)
    (hready : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport origin
        input.1)
    (state : Ix.CompileM.BlockState)
    (hstate : PreseedCollectFrameWF origin state)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    (hseen : PreseedSeenCovers compileEnv
      (preseedContextBlockEnv blockEnv params) origin
      (Ix.CompileM.univParamsKey params) [] acc) :
    HeterogeneousPreseedSeenSafe compileEnv blockEnv origin inputs acc
      state := by
  induction inputs generalizing state acc with
  | nil => trivial
  | cons input rest ih =>
      rcases input with ⟨source, sourceParams⟩
      have hparam : sourceParams = params :=
        hparams (source, sourceParams) (by simp)
      subst sourceParams
      have hsource : PreseedReady compileEnv
          (preseedContextBlockEnv blockEnv params) levelSupport origin
          source := hready (source, params) (by simp)
      have hrestParams : ∀ input ∈ rest, input.2 = params := by
        intro item hmem
        exact hparams item (by simp [hmem])
      have hrestReady : ∀ input ∈ rest,
          PreseedReady compileEnv
            (preseedContextBlockEnv blockEnv params) levelSupport origin
            input.1 := by
        intro item hmem
        exact hready item (by simp [hmem])
      have hstart : PreseedCollectStateWF compileEnv
          (preseedContextBlockEnv blockEnv params) levelSupport origin
          (preseedContextStartState state) :=
        hstate.preseedContextStartState_collectWF compileEnv blockEnv params
          levelSupport
      obtain ⟨headAcc, headState, hheadRun, hheadState, hheadWire,
          _hheadExt, _hheadCover, hheadSeen, _hheadSize⟩ :=
        collectExprTables_run_ready_covers_size compileEnv
          (preseedContextBlockEnv blockEnv params) origin hclosed
          hlevelFaithful hexprFaithful (Ix.CompileM.univParamsKey params)
          hsource acc hcollection [] hseen (by simp) hstart
      have hwrapped : Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.withUnivCtx params
            (Ix.CompileM.collectExprTables source
              (Ix.CompileM.univParamsKey params) acc)) =
          .ok (headAcc, headState) := by
        rw [withUnivCtx_run_eq]
        exact hheadRun
      constructor
      · exact hseen
      · intro acc' state' hrun
        rw [hwrapped] at hrun
        cases hrun
        exact ih hrestParams hrestReady headState hheadState.frame headAcc
          hheadWire hheadSeen

/-- Uniform root contexts discharge the explicit heterogeneous seen-set
boundary from source readiness.  This is the common mutual-declaration case:
the production list remains heterogeneous in shape, while its universe
parameter component is constant. -/
theorem heterogeneousPreseedSeenSafe_of_uniform
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inputs : List (Ix.Expr × List Ix.Name))
    (hparams : ∀ input ∈ inputs, input.2 = params)
    (hready : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv input.2) levelSupport
        (preseedContextStartState state) input.1)
    (hcanon : CanonUnivCacheWF state) :
    HeterogeneousPreseedSeenSafe compileEnv blockEnv
      (preseedContextStartState state) inputs (#[], #[], {}) state := by
  let origin := preseedContextStartState state
  have hframe : PreseedCollectFrameWF origin state :=
    ⟨rfl, rfl, hcanon, rfl⟩
  have hready' : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport origin
        input.1 := by
    intro input hmem
    simpa [hparams input hmem] using hready input hmem
  exact heterogeneousPreseedSeenSafe_of_uniform_aux compileEnv blockEnv
    origin params hclosed hlevelFaithful hexprFaithful inputs hparams
    hready' state hframe (#[], #[], {}) PreseedCollectionWireWF.empty
    (PreseedSeenCovers.empty compileEnv
      (preseedContextBlockEnv blockEnv params) origin
      (Ix.CompileM.univParamsKey params))

/-- The singleton root-collection phase used by axiom preseeding succeeds
from a sound canonical memo. Its result carries the complete collector frame
under the exact universe context installed for that root. -/
theorem collectPreseedExprs_singleton_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs [(source, params)] acc) =
        .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport
        (preseedContextStartState state) state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionSizeBound blockEnv.mutCtx source acc acc' := by
  let contextEnv := preseedContextBlockEnv blockEnv params
  let startState := preseedContextStartState state
  have hstart : PreseedCollectStateWF compileEnv contextEnv levelSupport
      startState startState := by
    exact preseedContextStartState_collectWF compileEnv blockEnv params
      levelSupport state hcanon
  obtain ⟨acc', state', hcollect, hstate', hcollection', hsize'⟩ :=
    collectExprTables_run_ready compileEnv contextEnv startState
      hclosed hfaithful (Ix.CompileM.univParamsKey params) hsource acc
      hcollection hstart
  refine ⟨acc', state', ?_, hstate', hcollection', ?_⟩
  rw [Ix.CompileM.collectPreseedExprs, run_bind, withUnivCtx_run_eq,
    hcollect]
  rfl
  exact hsize'

/-- The singleton production collection from empty arrays covers its source.
Digest/context hits are discharged by expression-key faithfulness and the
strict active-ancestor measure. -/
theorem collectPreseedExprs_singleton_run_ready_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state) :
    ∃ refs univs seen state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs
            [(source, params)] (#[], #[], {})) =
        .ok ((refs, univs, seen), state') ∧
      PreseedCollectStateWF compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport
        (preseedContextStartState state) state' ∧
      PreseedCollectionWireWF (refs, univs, seen) ∧
      PreseedCollectionCovers compileEnv
        (preseedContextBlockEnv blockEnv params)
        (preseedContextStartState state) refs univs source := by
  let contextEnv := preseedContextBlockEnv blockEnv params
  let startState := preseedContextStartState state
  let ctxKey := Ix.CompileM.univParamsKey params
  have hstart : PreseedCollectStateWF compileEnv contextEnv levelSupport
      startState startState := by
    exact preseedContextStartState_collectWF compileEnv blockEnv params
      levelSupport state hcanon
  obtain ⟨collected, state', hcollect, hstate', hcollection', hextends,
      hcovered, hseen'⟩ :=
    collectExprTables_run_ready_covers compileEnv contextEnv startState
      hclosed hlevelFaithful hexprFaithful ctxKey hsource (#[], #[], {})
      PreseedCollectionWireWF.empty []
      (PreseedSeenCovers.empty compileEnv contextEnv startState ctxKey)
      (by simp) hstart
  rcases collected with ⟨refs, univs, seen⟩
  refine ⟨refs, univs, seen, state', ?_, hstate', hcollection', hcovered⟩
  rw [Ix.CompileM.collectPreseedExprs, run_bind, withUnivCtx_run_eq,
    hcollect]
  rfl

/-- Two roots sharing one universe-parameter context retain the first root's
coverage while collecting the second. This is the production preseed shape of
definitions, theorems, and opaque declarations. -/
theorem collectPreseedExprs_pair_run_ready_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {first second : Ix.Expr}
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hsecond : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) second)
    (hcanon : CanonUnivCacheWF state) :
    ∃ refs univs seen state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs
            [(first, params), (second, params)] (#[], #[], {})) =
        .ok ((refs, univs, seen), state') ∧
      PreseedCollectStateWF compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport
        (preseedContextStartState state) state' ∧
      PreseedCollectionWireWF (refs, univs, seen) ∧
      PreseedCollectionCovers compileEnv
        (preseedContextBlockEnv blockEnv params)
        (preseedContextStartState state) refs univs first ∧
      PreseedCollectionCovers compileEnv
        (preseedContextBlockEnv blockEnv params)
        (preseedContextStartState state) refs univs second ∧
      PreseedPairCollectionSizeBound blockEnv.mutCtx first second
        (refs, univs, seen) := by
  let contextEnv := preseedContextBlockEnv blockEnv params
  let origin := preseedContextStartState state
  let ctxKey := Ix.CompileM.univParamsKey params
  have hstart : PreseedCollectStateWF compileEnv contextEnv levelSupport
      origin origin := by
    exact preseedContextStartState_collectWF compileEnv blockEnv params
      levelSupport state hcanon
  obtain ⟨firstAcc, firstState, hfirstRun, hfirstState, hfirstWire,
      hfirstExt, hfirstCover, hfirstSeen, hfirstSize⟩ :=
    collectExprTables_run_ready_covers_size compileEnv contextEnv origin
      hclosed hlevelFaithful hexprFaithful ctxKey hfirst (#[], #[], {})
      PreseedCollectionWireWF.empty []
      (PreseedSeenCovers.empty compileEnv contextEnv origin ctxKey)
      (by simp) hstart
  have hsecondStart : PreseedCollectStateWF compileEnv contextEnv levelSupport
      origin (preseedContextStartState firstState) :=
    hfirstState.preseedContextStartState
  obtain ⟨secondAcc, secondState, hsecondRun, hsecondState, hsecondWire,
      hsecondExt, hsecondCover, hsecondSeen, hsecondSize⟩ :=
    collectExprTables_run_ready_covers_size compileEnv contextEnv origin
      hclosed hlevelFaithful hexprFaithful ctxKey hsecond firstAcc
      hfirstWire [] hfirstSeen (by simp) hsecondStart
  have hfirstRefs : firstAcc.1.size ≤
      preseedRefCount blockEnv.mutCtx first := by
    simpa [contextEnv, preseedContextBlockEnv] using hfirstSize.refs
  have hfirstUnivs : firstAcc.2.1.size ≤ preseedUnivCount first := by
    simpa using hfirstSize.univs
  have hpairSize : PreseedPairCollectionSizeBound blockEnv.mutCtx
      first second secondAcc := by
    constructor
    · have hsecondRefs : secondAcc.1.size ≤ firstAcc.1.size +
          preseedRefCount blockEnv.mutCtx second := by
        simpa [contextEnv, preseedContextBlockEnv] using hsecondSize.refs
      omega
    · have hsecondUnivs : secondAcc.2.1.size ≤ firstAcc.2.1.size +
          preseedUnivCount second := by
        simpa using hsecondSize.univs
      omega
  rcases secondAcc with ⟨refs, univs, seen⟩
  refine ⟨refs, univs, seen, secondState, ?_, hsecondState, hsecondWire,
    hfirstCover.mono hsecondExt, hsecondCover, hpairSize⟩
  rw [Ix.CompileM.collectPreseedExprs, run_bind, withUnivCtx_run_eq,
    hfirstRun]
  simp only
  rw [Ix.CompileM.collectPreseedExprs, run_bind, withUnivCtx_run_eq,
    hsecondRun]
  rfl

private theorem collectPreseedExprs_roots_run_ready_covers_aux
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv contextEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hcontext : contextEnv = preseedContextBlockEnv blockEnv params)
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (sources : List Ix.Expr)
    (hready : ∀ source ∈ sources,
      PreseedReady compileEnv contextEnv levelSupport origin source)
    (state : Ix.CompileM.BlockState)
    (hstate : PreseedCollectStateWF compileEnv contextEnv levelSupport
      origin state)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    (hseen : PreseedSeenCovers compileEnv contextEnv origin
      (Ix.CompileM.univParamsKey params) [] acc) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs
            (sources.map fun source => (source, params)) acc) =
        .ok (acc', state') ∧
      PreseedCollectStateWF compileEnv contextEnv levelSupport
        origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionExtends acc acc' ∧
      (∀ source ∈ sources,
        PreseedCollectionCovers compileEnv contextEnv origin
          acc'.1 acc'.2.1 source) ∧
      PreseedSeenCovers compileEnv contextEnv origin
        (Ix.CompileM.univParamsKey params) [] acc' ∧
      PreseedRootCollectionSizeBound blockEnv.mutCtx sources acc acc' := by
  induction sources generalizing state acc with
  | nil =>
    exact ⟨acc, state, rfl, hstate, hcollection,
      PreseedCollectionExtends.refl acc, by simp, hseen,
      by constructor <;> simp [preseedRootRefCount,
        preseedRootUnivCount]⟩
  | cons source rest ih =>
    have hsource := hready source (by simp)
    have hrestReady : ∀ item ∈ rest,
        PreseedReady compileEnv contextEnv levelSupport origin item := by
      intro item hmem
      exact hready item (by simp [hmem])
    have hreset : PreseedCollectStateWF compileEnv contextEnv levelSupport
        origin (preseedContextStartState state) :=
      hstate.preseedContextStartState
    obtain ⟨headAcc, headState, hheadRun, hheadState, hheadWire,
        hheadExt, hheadCover, hheadSeen, hheadSize⟩ :=
      collectExprTables_run_ready_covers_size compileEnv contextEnv origin
        hclosed hlevelFaithful hexprFaithful
        (Ix.CompileM.univParamsKey params) hsource acc hcollection [] hseen
        (by simp) hreset
    obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hfinalWire,
        hrestExt, hrestCovers, hfinalSeen, hrestSize⟩ :=
      ih hrestReady headState hheadState headAcc hheadWire hheadSeen
    refine ⟨finalAcc, finalState, ?_, hfinalState, hfinalWire,
      hheadExt.trans hrestExt, ?_, hfinalSeen, ?_⟩
    · simp only [List.map_cons, Ix.CompileM.collectPreseedExprs]
      rw [run_bind, withUnivCtx_run_eq]
      rw [← hcontext, hheadRun]
      exact hrestRun
    · intro item hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst item
        exact hheadCover.mono hrestExt
      · exact hrestCovers item hmem
    · constructor
      · have hheadRefs : headAcc.1.size ≤
            acc.1.size + preseedRefCount blockEnv.mutCtx source := by
          simpa [hcontext, preseedContextBlockEnv] using hheadSize.refs
        have hrestRefs := hrestSize.refs
        simp only [preseedRootRefCount]
        omega
      · have hheadUnivs : headAcc.2.1.size ≤
            acc.2.1.size + preseedUnivCount source := hheadSize.univs
        have hrestUnivs := hrestSize.univs
        simp only [preseedRootUnivCount]
        omega

/-- A nonempty same-context root list is collected by the exact production
loop with coverage for every root and a summed structural cardinality bound. -/
theorem collectPreseedExprs_roots_run_ready_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (first : Ix.Expr) (rest : List Ix.Expr)
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hrest : ∀ source ∈ rest, PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state) :
    ∃ refs univs seen state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs
            ((first :: rest).map fun source => (source, params))
            (#[], #[], {})) =
        .ok ((refs, univs, seen), state') ∧
      PreseedCollectStateWF compileEnv
        (preseedContextBlockEnv blockEnv params) levelSupport
        (preseedContextStartState state) state' ∧
      PreseedCollectionWireWF (refs, univs, seen) ∧
      (∀ source ∈ first :: rest,
        PreseedCollectionCovers compileEnv
          (preseedContextBlockEnv blockEnv params)
          (preseedContextStartState state) refs univs source) ∧
      PreseedRootCollectionSizeBound blockEnv.mutCtx (first :: rest)
        (#[], #[], {}) (refs, univs, seen) := by
  let contextEnv := preseedContextBlockEnv blockEnv params
  let origin := preseedContextStartState state
  let ctxKey := Ix.CompileM.univParamsKey params
  have hstart : PreseedCollectStateWF compileEnv contextEnv levelSupport
      origin origin := by
    exact preseedContextStartState_collectWF compileEnv blockEnv params
      levelSupport state hcanon
  obtain ⟨firstAcc, firstState, hfirstRun, hfirstState, hfirstWire,
      hfirstExt, hfirstCover, hfirstSeen, hfirstSize⟩ :=
    collectExprTables_run_ready_covers_size compileEnv contextEnv origin
      hclosed hlevelFaithful hexprFaithful ctxKey hfirst (#[], #[], {})
      PreseedCollectionWireWF.empty []
      (PreseedSeenCovers.empty compileEnv contextEnv origin ctxKey)
      (by simp) hstart
  obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hfinalWire,
      hrestExt, hrestCovers, hfinalSeen, hrestSize⟩ :=
    collectPreseedExprs_roots_run_ready_covers_aux compileEnv blockEnv
      contextEnv origin params rfl hclosed hlevelFaithful hexprFaithful rest
      hrest firstState hfirstState firstAcc hfirstWire hfirstSeen
  rcases finalAcc with ⟨refs, univs, seen⟩
  refine ⟨refs, univs, seen, finalState, ?_, hfinalState,
    hfinalWire, ?_, ?_⟩
  · simp only [List.map_cons, Ix.CompileM.collectPreseedExprs]
    rw [run_bind, withUnivCtx_run_eq, hfirstRun]
    exact hrestRun
  · intro source hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · subst source
      exact hfirstCover.mono hrestExt
    · exact hrestCovers source hmem
  · constructor
    · have hfirstRefs : firstAcc.1.size ≤
          preseedRefCount blockEnv.mutCtx first := by
        simpa [contextEnv, preseedContextBlockEnv] using hfirstSize.refs
      have hrestRefs : refs.size ≤ firstAcc.1.size +
          preseedRootRefCount blockEnv.mutCtx rest := by
        simpa using hrestSize.refs
      simp only [preseedRootRefCount]
      omega
    · have hfirstUnivs : firstAcc.2.1.size ≤
          preseedUnivCount first := by
        simpa using hfirstSize.univs
      have hrestUnivs : univs.size ≤ firstAcc.2.1.size +
          preseedRootUnivCount rest := by
        simpa using hrestSize.univs
      simp only [preseedRootUnivCount]
      omega

private theorem collectPreseedExprs_inputs_run_ready_covers_aux
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (origin : Ix.CompileM.BlockState) {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inputs : List (Ix.Expr × List Ix.Name))
    (hready : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv input.2) levelSupport origin
        input.1)
    (state : Ix.CompileM.BlockState)
    (hstate : PreseedCollectFrameWF origin state)
    (acc : Ix.CompileM.ExprTableCollection)
    (hcollection : PreseedCollectionWireWF acc)
    (hseen : HeterogeneousPreseedSeenSafe compileEnv blockEnv origin
      inputs acc state) :
    ∃ acc' state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs inputs acc) =
        .ok (acc', state') ∧
      PreseedCollectFrameWF origin state' ∧
      PreseedCollectionWireWF acc' ∧
      PreseedCollectionExtends acc acc' ∧
      (∀ input ∈ inputs,
        PreseedCollectionCovers compileEnv
          (preseedContextBlockEnv blockEnv input.2) origin
          acc'.1 acc'.2.1 input.1) ∧
      PreseedInputCollectionSizeBound blockEnv.mutCtx inputs acc acc' := by
  induction inputs generalizing state acc with
  | nil =>
      exact ⟨acc, state, rfl, hstate, hcollection,
        PreseedCollectionExtends.refl acc, by simp,
        by constructor <;> simp [preseedInputRefCount,
          preseedInputUnivCount]⟩
  | cons input rest ih =>
      rcases input with ⟨source, params⟩
      let contextEnv := preseedContextBlockEnv blockEnv params
      let ctxKey := Ix.CompileM.univParamsKey params
      have hsource : PreseedReady compileEnv contextEnv levelSupport origin
          source := by
        exact hready (source, params) (by simp)
      have hrestReady : ∀ input ∈ rest,
          PreseedReady compileEnv
            (preseedContextBlockEnv blockEnv input.2) levelSupport origin
            input.1 := by
        intro item hmem
        exact hready item (by simp [hmem])
      have hstart : PreseedCollectStateWF compileEnv contextEnv levelSupport
          origin (preseedContextStartState state) := by
        exact hstate.preseedContextStartState_collectWF compileEnv blockEnv
          params levelSupport
      obtain ⟨headAcc, headState, hheadRun, hheadState, hheadWire,
          hheadExt, hheadCover, hheadSeen, hheadSize⟩ :=
        collectExprTables_run_ready_covers_size compileEnv contextEnv origin
          hclosed hlevelFaithful hexprFaithful ctxKey hsource acc hcollection
          [] hseen.1 (by simp) hstart
      have hheadWrapped : Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.withUnivCtx params
            (Ix.CompileM.collectExprTables source ctxKey acc)) =
          .ok (headAcc, headState) := by
        rw [withUnivCtx_run_eq]
        exact hheadRun
      have hrestSeen : HeterogeneousPreseedSeenSafe compileEnv blockEnv
          origin rest headAcc headState :=
        hseen.2 headAcc headState hheadWrapped
      obtain ⟨finalAcc, finalState, hrestRun, hfinalState, hfinalWire,
          hrestExt, hrestCovers, hrestSize⟩ :=
        ih hrestReady headState hheadState.frame headAcc hheadWire hrestSeen
      refine ⟨finalAcc, finalState, ?_, hfinalState, hfinalWire,
        hheadExt.trans hrestExt, ?_, ?_⟩
      · unfold Ix.CompileM.collectPreseedExprs
        rw [run_bind, hheadWrapped]
        exact hrestRun
      · intro item hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst item
          exact hheadCover.mono hrestExt
        · exact hrestCovers item hmem
      · constructor
        · have hheadRefs : headAcc.1.size ≤ acc.1.size +
              preseedRefCount blockEnv.mutCtx source := by
            simpa [contextEnv, preseedContextBlockEnv] using hheadSize.refs
          have hrestRefs := hrestSize.refs
          simp only [preseedInputRefCount]
          omega
        · have hheadUnivs : headAcc.2.1.size ≤ acc.2.1.size +
              preseedUnivCount source := hheadSize.univs
          have hrestUnivs := hrestSize.univs
          simp only [preseedInputUnivCount]
          omega

/-- Heterogeneous roots are collected in their own universe contexts by the
exact production recursion. Source readiness and the explicit shared-seen
collision discipline yield coverage for every `(source, params)` input and a
summed structural capacity bound. -/
theorem collectPreseedExprs_inputs_run_ready_covers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inputs : List (Ix.Expr × List Ix.Name))
    (hready : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv input.2) levelSupport
        (preseedContextStartState state) input.1)
    (hcanon : CanonUnivCacheWF state)
    (hseen : HeterogeneousPreseedSeenSafe compileEnv blockEnv
      (preseedContextStartState state) inputs (#[], #[], {}) state) :
    ∃ refs univs seen state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.collectPreseedExprs inputs (#[], #[], {})) =
        .ok ((refs, univs, seen), state') ∧
      PreseedCollectFrameWF (preseedContextStartState state) state' ∧
      PreseedCollectionWireWF (refs, univs, seen) ∧
      (∀ input ∈ inputs,
        PreseedCollectionCovers compileEnv
          (preseedContextBlockEnv blockEnv input.2)
          (preseedContextStartState state) refs univs input.1) ∧
      PreseedInputCollectionSizeBound blockEnv.mutCtx inputs
        (#[], #[], {}) (refs, univs, seen) := by
  let origin := preseedContextStartState state
  have hstart : PreseedCollectFrameWF origin state := by
    exact ⟨rfl, rfl, hcanon, rfl⟩
  obtain ⟨finalAcc, finalState, hrun, hfinalState, hwire, hextends,
      hcovers, hsize⟩ :=
    collectPreseedExprs_inputs_run_ready_covers_aux compileEnv blockEnv
      origin hclosed hlevelFaithful hexprFaithful inputs hready state hstart
      (#[], #[], {}) PreseedCollectionWireWF.empty hseen
  rcases finalAcc with ⟨refs, univs, seen⟩
  exact ⟨refs, univs, seen, finalState, hrun, hfinalState, hwire,
    hcovers, hsize⟩

/-- Canonicalizing a collected universe list cannot fail from a sound memo.
It appends exactly the deterministic canonical forms and changes none of the
expression compiler's primary tables or non-canonical caches. -/
theorem canonPreseedUnivs_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (univs : List Ixon.Univ) (initial : Array Ixon.Univ)
    {state : Ix.CompileM.BlockState} (hstate : CanonUnivCacheWF state) :
    ∃ result state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.canonPreseedUnivs univs initial) =
        .ok (result, state') ∧
      result.toList = initial.toList ++ univs.map Ixon.canonUniv ∧
      CanonUnivCacheWF state' ∧
      exprTableView state' = exprTableView state ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.arena = state.arena := by
  induction univs generalizing initial state with
  | nil =>
    exact ⟨initial, state, rfl, by simp, hstate, rfl, rfl, rfl, rfl⟩
  | cons u rest ih =>
    obtain ⟨canonState, hcanonRun, hcanonState, hcanonTables,
        hcanonExprCache, hcanonUnivCache, hcanonArena⟩ :=
      canonUnivCached_run_refines compileEnv blockEnv hstate u
    obtain ⟨result, state', hrestRun, hresult, hstate', hrestTables,
        hrestExprCache, hrestUnivCache, hrestArena⟩ :=
      ih (initial := initial.push (Ixon.canonUniv u)) hcanonState
    refine ⟨result, state', ?_, ?_, hstate',
      hrestTables.trans hcanonTables,
      hrestExprCache.trans hcanonExprCache,
      hrestUnivCache.trans hcanonUnivCache,
      hrestArena.trans hcanonArena⟩
    · rw [Ix.CompileM.canonPreseedUnivs, run_bind, hcanonRun]
      exact hrestRun
    · simpa [List.map, List.append_assoc] using hresult

/-- Reference-table soundness together with the exact address payload
condition required by the constant codec. -/
structure PreseedRefTableWF (state : Ix.CompileM.BlockState) : Prop where
  table : RefTableWF state
  wire : ∀ addr ∈ state.refs, addr.hash.size = 32

theorem PreseedRefTableWF.empty :
    PreseedRefTableWF (default : Ix.CompileM.BlockState) := by
  refine ⟨RefTableWF.empty, ?_⟩
  intro addr hmem
  exact (Array.not_mem_empty addr hmem).elim

theorem PreseedRefTableWF.of_fields_eq
    {before after : Ix.CompileM.BlockState}
    (hbefore : PreseedRefTableWF before)
    (hrefs : after.refs = before.refs)
    (hindex : after.refsIndex = before.refsIndex) :
    PreseedRefTableWF after := by
  constructor
  · constructor
    · simpa only [hrefs] using hbefore.table.size
    · intro addr idx hget
      have hget' : before.refsIndex.get? addr = some idx := by
        simpa only [hindex] using hget
      simpa only [hrefs] using hbefore.table.index hget'
  · intro addr hmem
    exact hbefore.wire addr (by simpa only [hrefs] using hmem)

theorem PreseedRefTableWF.of_exprTableView_eq
    {before after : Ix.CompileM.BlockState}
    (hbefore : PreseedRefTableWF before)
    (hview : exprTableView after = exprTableView before) :
    PreseedRefTableWF after := by
  have hrefs : after.refs = before.refs :=
    congrArg ExprTableView.refs hview
  have hindex : after.refsIndex = before.refsIndex :=
    congrArg ExprTableView.refsIndex hview
  constructor
  · constructor
    · simpa only [hrefs] using hbefore.table.size
    · intro addr idx hget
      have hget' : before.refsIndex.get? addr = some idx := by
        simpa only [hindex] using hget
      simpa only [hrefs] using hbefore.table.index hget'
  · intro addr hmem
    exact hbefore.wire addr (by simpa only [hrefs] using hmem)

/-- Interning one wire-safe address preserves the combined reference-table
invariant and grows the table by at most one slot. -/
theorem PreseedRefTableWF.intern
    {state : Ix.CompileM.BlockState} (hstate : PreseedRefTableWF state)
    (addr : Address) (haddr : addr.hash.size = 32)
    (hroom : state.refs.size + 1 < UInt64.size) :
    let state' := (state.internRef addr).1
    PreseedRefTableWF state' ∧
      state'.refs.size ≤ state.refs.size + 1 ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.univs = state.univs := by
  simp only [Ix.CompileM.BlockState.internRef]
  split
  next idx hindex =>
    exact ⟨hstate, by simp, rfl, rfl, rfl, rfl, rfl⟩
  next hmissing =>
    have htable :=
      Ix.Compile.Verify.BlockState.internRef_wf hstate.table addr hroom
    simp only [Ix.CompileM.BlockState.internRef, hmissing] at htable
    refine ⟨⟨htable.1, ?_⟩, by simp, rfl, rfl, rfl, rfl, rfl⟩
    intro value hmem
    simp only [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate.wire value hmem
    · exact haddr

/-- The sorted reference commit is total under a conservative one-slot-per-
input capacity bound. It preserves wire/table soundness and all expression
caches, the universe table, and the arena. Adjacent duplicates merely make
the actual growth smaller than the bound. -/
theorem internPreseedRefs_run_wf
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (refs : List Address) (previous : Option Address)
    {state : Ix.CompileM.BlockState} (hstate : PreseedRefTableWF state)
    (hwire : ∀ addr ∈ refs, addr.hash.size = 32)
    (hroom : state.refs.size + refs.length < UInt64.size) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internPreseedRefs refs previous) = .ok ((), state') ∧
      PreseedRefTableWF state' ∧
      state'.refs.size ≤ state.refs.size + refs.length ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.univs = state.univs := by
  induction refs generalizing previous state with
  | nil =>
    exact ⟨state, rfl, hstate, by simp, rfl, rfl, rfl, rfl, rfl⟩
  | cons addr rest ih =>
    have haddr : addr.hash.size = 32 := hwire addr (by simp)
    have hrestWire : ∀ value ∈ rest, value.hash.size = 32 := by
      intro value hmem
      exact hwire value (by simp [hmem])
    cases hnew : previous != some addr with
    | false =>
      have hrestRoom : state.refs.size + rest.length < UInt64.size := by
        simp only [List.length_cons] at hroom
        omega
      obtain ⟨state', hrun, hstate', hgrowth, hexpr, huniv,
          hcanon, harena, hunivs⟩ :=
        ih (previous := some addr) hstate hrestWire hrestRoom
      refine ⟨state', ?_, hstate', ?_, hexpr, huniv, hcanon, harena,
        hunivs⟩
      · rw [Ix.CompileM.internPreseedRefs, hnew]
        exact hrun
      · simp only [List.length_cons]
        omega
    | true =>
      have honeRoom : state.refs.size + 1 < UInt64.size := by
        simp only [List.length_cons] at hroom
        omega
      let next := (state.internRef addr).1
      obtain ⟨hnext, hnextGrowth, hnextExpr, hnextUniv, hnextCanon,
          hnextArena, hnextUnivs⟩ := hstate.intern addr haddr honeRoom
      have hrestRoom : next.refs.size + rest.length < UInt64.size := by
        dsimp only [next] at hnextGrowth ⊢
        simp only [List.length_cons] at hroom
        omega
      obtain ⟨state', hrun, hstate', hgrowth, hexpr, huniv,
          hcanon, harena, hunivs⟩ :=
        ih (previous := some addr) hnext hrestWire hrestRoom
      refine ⟨state', ?_, hstate', ?_,
        hexpr.trans hnextExpr,
        huniv.trans hnextUniv,
        hcanon.trans hnextCanon,
        harena.trans hnextArena,
        hunivs.trans hnextUnivs⟩
      · rw [Ix.CompileM.internPreseedRefs, hnew]
        simp only [if_pos]
        rw [run_bind, run_discard_internRef]
        change Ix.CompileM.CompileM.run compileEnv blockEnv next
          (Ix.CompileM.internPreseedRefs rest (some addr)) = _
        exact hrun
      · simp only [List.length_cons]
        omega

private theorem internRef_frame
    (state : Ix.CompileM.BlockState) (addr : Address) :
    let state' := (state.internRef addr).1
    state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.univs = state.univs := by
  simp only [Ix.CompileM.BlockState.internRef]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Reference interning cannot throw even without a logical capacity bound;
the bound is needed only to prove lossless `UInt64` indices. -/
theorem internPreseedRefs_run_total
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (refs : List Address) (previous : Option Address)
    (state : Ix.CompileM.BlockState) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internPreseedRefs refs previous) = .ok ((), state') ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.univs = state.univs := by
  induction refs generalizing previous state with
  | nil => exact ⟨state, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons addr rest ih =>
    cases hnew : previous != some addr with
    | false =>
      obtain ⟨state', hrun, hexpr, huniv, hcanon, harena, hunivs⟩ :=
        ih (previous := some addr) state
      refine ⟨state', ?_, hexpr, huniv, hcanon, harena, hunivs⟩
      rw [Ix.CompileM.internPreseedRefs, hnew]
      exact hrun
    | true =>
      let next := (state.internRef addr).1
      obtain ⟨hnextExpr, hnextUniv, hnextCanon, hnextArena, hnextUnivs⟩ :=
        internRef_frame state addr
      obtain ⟨state', hrun, hexpr, huniv, hcanon, harena, hunivs⟩ :=
        ih (previous := some addr) next
      refine ⟨state', ?_,
        hexpr.trans hnextExpr,
        huniv.trans hnextUniv,
        hcanon.trans hnextCanon,
        harena.trans hnextArena,
        hunivs.trans hnextUnivs⟩
      rw [Ix.CompileM.internPreseedRefs, hnew]
      simp only [if_pos]
      rw [run_bind, run_discard_internRef]
      change Ix.CompileM.CompileM.run compileEnv blockEnv next
        (Ix.CompileM.internPreseedRefs rest (some addr)) = _
      exact hrun

/-- Reference commits leave the entire universe primary table untouched,
including its lookup map. -/
theorem internPreseedRefs_run_univTableFrame
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (refs : List Address) (previous : Option Address)
    {state state' : Ix.CompileM.BlockState}
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.internPreseedRefs refs previous) = .ok ((), state')) :
    state'.univs = state.univs ∧
      state'.univsIndex = state.univsIndex := by
  induction refs generalizing previous state state' with
  | nil =>
    simp only [Ix.CompileM.internPreseedRefs] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩
  | cons addr rest ih =>
    cases hnew : previous != some addr with
    | false =>
      rw [Ix.CompileM.internPreseedRefs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      exact ih (previous := some addr) hrun
    | true =>
      let next := (state.internRef addr).1
      rw [Ix.CompileM.internPreseedRefs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        discard <| Ix.CompileM.internRef addr
        Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      rw [run_bind, run_discard_internRef] at hrun
      have hrest := ih (previous := some addr) hrun
      have hnext : next.univs = state.univs ∧
          next.univsIndex = state.univsIndex := by
        simp only [next, Ix.CompileM.BlockState.internRef]
        split <;> exact ⟨rfl, rfl⟩
      exact ⟨hrest.1.trans hnext.1, hrest.2.trans hnext.2⟩

theorem internPreseedRefs_run_resolutionFrame
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (refs : List Address) (previous : Option Address)
    {state state' : Ix.CompileM.BlockState}
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.internPreseedRefs refs previous) = .ok ((), state')) :
    state'.blockNameToAddr = state.blockNameToAddr ∧
      state'.auxNameToAddr = state.auxNameToAddr := by
  induction refs generalizing previous state state' with
  | nil =>
    simp only [Ix.CompileM.internPreseedRefs] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩
  | cons addr rest ih =>
    cases hnew : previous != some addr with
    | false =>
      rw [Ix.CompileM.internPreseedRefs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      exact ih (previous := some addr) hrun
    | true =>
      let next := (state.internRef addr).1
      rw [Ix.CompileM.internPreseedRefs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        discard <| Ix.CompileM.internRef addr
        Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      rw [run_bind, run_discard_internRef] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv next
        (Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      have hrest := ih (previous := some addr) hrun
      have hnext : next.blockNameToAddr = state.blockNameToAddr ∧
          next.auxNameToAddr = state.auxNameToAddr := by
        simp only [next, Ix.CompileM.BlockState.internRef]
        split <;> exact ⟨rfl, rfl⟩
      exact ⟨hrest.1.trans hnext.1, hrest.2.trans hnext.2⟩

/-- Every reference presented to the adjacent-deduplicating commit receives
an index, while all pre-existing successful lookups are preserved. The
`previous` premise accounts for a skipped first entry; production calls this
theorem with `none`, where that premise is vacuous. -/
theorem internPreseedRefs_run_indexed
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (refs : List Address) (previous : Option Address)
    {state state' : Ix.CompileM.BlockState}
    (hprevious : ∀ addr, previous = some addr →
      ∃ idx, state.refsIndex.get? addr = some idx)
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.internPreseedRefs refs previous) = .ok ((), state')) :
    (∀ {addr idx}, state.refsIndex.get? addr = some idx →
      state'.refsIndex.get? addr = some idx) ∧
    (∀ addr ∈ refs, ∃ idx, state'.refsIndex.get? addr = some idx) := by
  induction refs generalizing previous state state' with
  | nil =>
    simp only [Ix.CompileM.internPreseedRefs] at hrun
    cases hrun
    refine ⟨fun hget => hget, ?_⟩
    intro addr hmem
    simp at hmem
  | cons addr rest ih =>
    cases hnew : previous != some addr with
    | false =>
      rw [Ix.CompileM.internPreseedRefs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      have heq : previous = some addr := by simpa using hnew
      have hhead := hprevious addr heq
      have hnextPrevious : ∀ queried, some addr = some queried →
          ∃ idx, state.refsIndex.get? queried = some idx := by
        intro queried hqueried
        cases hqueried
        exact hhead
      obtain ⟨hpreserve, hrest⟩ :=
        ih (previous := some addr) hnextPrevious hrun
      refine ⟨hpreserve, ?_⟩
      intro queried hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · obtain ⟨idx, hidx⟩ := hhead
        exact ⟨idx, hpreserve hidx⟩
      · exact hrest queried hmem
    | true =>
      let next := (state.internRef addr).1
      rw [Ix.CompileM.internPreseedRefs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        discard <| Ix.CompileM.internRef addr
        Ix.CompileM.internPreseedRefs rest (some addr)) =
          .ok ((), state') at hrun
      rw [run_bind, run_discard_internRef] at hrun
      have hhead : ∃ idx, next.refsIndex.get? addr = some idx := by
        let result := state.internRef addr
        refine ⟨result.2, ?_⟩
        exact internRef_own_index state addr
      have hnextPrevious : ∀ queried, some addr = some queried →
          ∃ idx, next.refsIndex.get? queried = some idx := by
        intro queried hqueried
        cases hqueried
        exact hhead
      obtain ⟨hpreserveNext, hrest⟩ :=
        ih (previous := some addr) hnextPrevious hrun
      refine ⟨?_, ?_⟩
      · intro queried idx hget
        exact hpreserveNext (internRef_preserves_index state addr queried idx
          hget)
      · intro queried hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · obtain ⟨idx, hidx⟩ := hhead
          exact ⟨idx, hpreserveNext hidx⟩
        · exact hrest queried hmem
/-- Universe-table soundness together with the universe codec's recursive
wire condition. -/
structure PreseedUnivTableWF (state : Ix.CompileM.BlockState) : Prop where
  table : UnivTableWF state
  wire : ∀ u ∈ state.univs, Codec.Ixon.Univ.WireWF u

theorem PreseedUnivTableWF.empty :
    PreseedUnivTableWF (default : Ix.CompileM.BlockState) := by
  refine ⟨UnivTableWF.empty, ?_⟩
  intro u hmem
  exact (Array.not_mem_empty u hmem).elim

theorem PreseedUnivTableWF.of_fields_eq
    {before after : Ix.CompileM.BlockState}
    (hbefore : PreseedUnivTableWF before)
    (hunivs : after.univs = before.univs)
    (hindex : after.univsIndex = before.univsIndex) :
    PreseedUnivTableWF after := by
  constructor
  · constructor
    · simpa only [hunivs] using hbefore.table.size
    · intro u idx hget
      have hget' : before.univsIndex.get? u = some idx := by
        simpa only [hindex] using hget
      simpa only [hunivs] using hbefore.table.index hget'
  · intro u hmem
    exact hbefore.wire u (by simpa only [hunivs] using hmem)

theorem PreseedUnivTableWF.of_exprTableView_eq
    {before after : Ix.CompileM.BlockState}
    (hbefore : PreseedUnivTableWF before)
    (hview : exprTableView after = exprTableView before) :
    PreseedUnivTableWF after := by
  have hunivs : after.univs = before.univs :=
    congrArg ExprTableView.univs hview
  have hindex : after.univsIndex = before.univsIndex :=
    congrArg ExprTableView.univsIndex hview
  constructor
  · constructor
    · simpa only [hunivs] using hbefore.table.size
    · intro u idx hget
      have hget' : before.univsIndex.get? u = some idx := by
        simpa only [hindex] using hget
      simpa only [hunivs] using hbefore.table.index hget'
  · intro u hmem
    exact hbefore.wire u (by simpa only [hunivs] using hmem)

/-- The two commit invariants are exactly the primary table component needed
by the production constant codec. -/
theorem BlockWireTablesWF.of_preseed
    {state : Ix.CompileM.BlockState}
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state) : BlockWireTablesWF state :=
  { refsCount := hrefs.table.size
    refs := hrefs.wire
    univsCount := hunivs.table.size
    univs := hunivs.wire }

/-- Interning one wire-safe universe preserves the combined universe-table
invariant and grows the primary table by at most one slot. -/
theorem PreseedUnivTableWF.intern
    {state : Ix.CompileM.BlockState} (hstate : PreseedUnivTableWF state)
    (u : Ixon.Univ) (hu : Codec.Ixon.Univ.WireWF u)
    (hroom : state.univs.size + 1 < UInt64.size) :
    let state' := (state.internUniv u).1
    PreseedUnivTableWF state' ∧
      state'.univs.size ≤ state.univs.size + 1 ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.refs = state.refs := by
  simp only [Ix.CompileM.BlockState.internUniv]
  split
  next idx hindex =>
    exact ⟨hstate, by simp, rfl, rfl, rfl, rfl, rfl⟩
  next hmissing =>
    have htable :=
      Ix.Compile.Verify.BlockState.internUniv_wf hstate.table u hroom
    simp only [Ix.CompileM.BlockState.internUniv, hmissing] at htable
    refine ⟨⟨htable.1, ?_⟩, by simp, rfl, rfl, rfl, rfl, rfl⟩
    intro value hmem
    simp only [Array.mem_push] at hmem
    rcases hmem with hmem | rfl
    · exact hstate.wire value hmem
    · exact hu

/-- The sorted canonical-universe commit is total under the analogous
one-slot-per-input capacity bound and preserves every non-universe component
needed by ordinary expression compilation. -/
theorem internPreseedUnivs_run_wf
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray)
    {state : Ix.CompileM.BlockState} (hstate : PreseedUnivTableWF state)
    (hwire : ∀ entry ∈ univs, Codec.Ixon.Univ.WireWF entry.2)
    (hroom : state.univs.size + univs.length < UInt64.size) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internPreseedUnivs univs previous) =
        .ok ((), state') ∧
      PreseedUnivTableWF state' ∧
      state'.univs.size ≤ state.univs.size + univs.length ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.refs = state.refs := by
  induction univs generalizing previous state with
  | nil =>
    exact ⟨state, rfl, hstate, by simp, rfl, rfl, rfl, rfl, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨key, u⟩
    have hu : Codec.Ixon.Univ.WireWF u := hwire (key, u) (by simp)
    have hrestWire :
        ∀ value ∈ rest, Codec.Ixon.Univ.WireWF value.2 := by
      intro value hmem
      exact hwire value (by simp [hmem])
    cases hnew : previous != some key with
    | false =>
      have hrestRoom : state.univs.size + rest.length < UInt64.size := by
        simp only [List.length_cons] at hroom
        omega
      obtain ⟨state', hrun, hstate', hgrowth, hexpr, huniv,
          hcanon, harena, hrefs⟩ :=
        ih (previous := some key) hstate hrestWire hrestRoom
      refine ⟨state', ?_, hstate', ?_, hexpr, huniv, hcanon, harena,
        hrefs⟩
      · rw [Ix.CompileM.internPreseedUnivs, hnew]
        exact hrun
      · simp only [List.length_cons]
        omega
    | true =>
      have honeRoom : state.univs.size + 1 < UInt64.size := by
        simp only [List.length_cons] at hroom
        omega
      let next := (state.internUniv u).1
      obtain ⟨hnext, hnextGrowth, hnextExpr, hnextUniv, hnextCanon,
          hnextArena, hnextRefs⟩ := hstate.intern u hu honeRoom
      have hrestRoom : next.univs.size + rest.length < UInt64.size := by
        dsimp only [next] at hnextGrowth ⊢
        simp only [List.length_cons] at hroom
        omega
      obtain ⟨state', hrun, hstate', hgrowth, hexpr, huniv,
          hcanon, harena, hrefs⟩ :=
        ih (previous := some key) hnext hrestWire hrestRoom
      refine ⟨state', ?_, hstate', ?_,
        hexpr.trans hnextExpr,
        huniv.trans hnextUniv,
        hcanon.trans hnextCanon,
        harena.trans hnextArena,
        hrefs.trans hnextRefs⟩
      · rw [Ix.CompileM.internPreseedUnivs, hnew]
        simp only [if_pos]
        rw [run_bind, run_discard_internUniv]
        change Ix.CompileM.CompileM.run compileEnv blockEnv next
          (Ix.CompileM.internPreseedUnivs rest (some key)) = _
        exact hrun
      · simp only [List.length_cons]
        omega

private theorem internUniv_frame
    (state : Ix.CompileM.BlockState) (u : Ixon.Univ) :
    let state' := (state.internUniv u).1
    state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.refs = state.refs := by
  simp only [Ix.CompileM.BlockState.internUniv]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical-universe interning is likewise total independently of the
lossless-index capacity condition. -/
theorem internPreseedUnivs_run_total
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray) (state : Ix.CompileM.BlockState) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.internPreseedUnivs univs previous) =
        .ok ((), state') ∧
      state'.exprCache = state.exprCache ∧
      state'.univCache = state.univCache ∧
      state'.canonUnivCache = state.canonUnivCache ∧
      state'.arena = state.arena ∧
      state'.refs = state.refs := by
  induction univs generalizing previous state with
  | nil => exact ⟨state, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨key, u⟩
    cases hnew : previous != some key with
    | false =>
      obtain ⟨state', hrun, hexpr, huniv, hcanon, harena, hrefs⟩ :=
        ih (previous := some key) state
      refine ⟨state', ?_, hexpr, huniv, hcanon, harena, hrefs⟩
      rw [Ix.CompileM.internPreseedUnivs, hnew]
      exact hrun
    | true =>
      let next := (state.internUniv u).1
      obtain ⟨hnextExpr, hnextUniv, hnextCanon, hnextArena, hnextRefs⟩ :=
        internUniv_frame state u
      obtain ⟨state', hrun, hexpr, huniv, hcanon, harena, hrefs⟩ :=
        ih (previous := some key) next
      refine ⟨state', ?_,
        hexpr.trans hnextExpr,
        huniv.trans hnextUniv,
        hcanon.trans hnextCanon,
        harena.trans hnextArena,
        hrefs.trans hnextRefs⟩
      rw [Ix.CompileM.internPreseedUnivs, hnew]
      simp only [if_pos]
      rw [run_bind, run_discard_internUniv]
      change Ix.CompileM.CompileM.run compileEnv blockEnv next
        (Ix.CompileM.internPreseedUnivs rest (some key)) = _
      exact hrun

/-- Universe commits dually leave the entire reference primary table
untouched. -/
theorem internPreseedUnivs_run_refTableFrame
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray)
    {state state' : Ix.CompileM.BlockState}
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.internPreseedUnivs univs previous) = .ok ((), state')) :
    state'.refs = state.refs ∧
      state'.refsIndex = state.refsIndex := by
  induction univs generalizing previous state state' with
  | nil =>
    simp only [Ix.CompileM.internPreseedUnivs] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨key, u⟩
    cases hnew : previous != some key with
    | false =>
      rw [Ix.CompileM.internPreseedUnivs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      exact ih (previous := some key) hrun
    | true =>
      let next := (state.internUniv u).1
      rw [Ix.CompileM.internPreseedUnivs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        discard <| Ix.CompileM.internUniv u
        Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      rw [run_bind, run_discard_internUniv] at hrun
      have hrest := ih (previous := some key) hrun
      have hnext : next.refs = state.refs ∧
          next.refsIndex = state.refsIndex := by
        simp only [next, Ix.CompileM.BlockState.internUniv]
        split <;> exact ⟨rfl, rfl⟩
      exact ⟨hrest.1.trans hnext.1, hrest.2.trans hnext.2⟩

theorem internPreseedUnivs_run_resolutionFrame
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray)
    {state state' : Ix.CompileM.BlockState}
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.internPreseedUnivs univs previous) = .ok ((), state')) :
    state'.blockNameToAddr = state.blockNameToAddr ∧
      state'.auxNameToAddr = state.auxNameToAddr := by
  induction univs generalizing previous state state' with
  | nil =>
    simp only [Ix.CompileM.internPreseedUnivs] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨key, u⟩
    cases hnew : previous != some key with
    | false =>
      rw [Ix.CompileM.internPreseedUnivs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      exact ih (previous := some key) hrun
    | true =>
      let next := (state.internUniv u).1
      rw [Ix.CompileM.internPreseedUnivs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        discard <| Ix.CompileM.internUniv u
        Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      rw [run_bind, run_discard_internUniv] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv next
        (Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      have hrest := ih (previous := some key) hrun
      have hnext : next.blockNameToAddr = state.blockNameToAddr ∧
          next.auxNameToAddr = state.auxNameToAddr := by
        simp only [next, Ix.CompileM.BlockState.internUniv]
        split <;> exact ⟨rfl, rfl⟩
      exact ⟨hrest.1.trans hnext.1, hrest.2.trans hnext.2⟩

theorem univSortKey_injective_wire
    {left right : Ixon.Univ}
    (hleft : Codec.Ixon.Univ.WireWF left)
    (hright : Codec.Ixon.Univ.WireWF right)
    (hkey : Ix.CompileM.univSortKey left =
      Ix.CompileM.univSortKey right) :
    left = right := by
  change Ixon.serUniv left = Ixon.serUniv right at hkey
  have hdecode := Codec.Ixon.Univ.deUniv_serUniv left hleft
  have hdecodeRight := Codec.Ixon.Univ.deUniv_serUniv right hright
  rw [hkey, hdecodeRight] at hdecode
  exact (Except.ok.inj hdecode).symm

/-- Every canonical universe presented to the keyed adjacent-deduplicating
commit receives an index. Equal skipped keys denote equal values because the
universe codec is injective on its wire domain. -/
theorem internPreseedUnivs_run_indexed
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray)
    {state state' : Ix.CompileM.BlockState}
    (hwire : ∀ entry ∈ univs, Codec.Ixon.Univ.WireWF entry.2)
    (hkeys : ∀ entry ∈ univs,
      entry.1 = Ix.CompileM.univSortKey entry.2)
    (hprevious : ∀ key, previous = some key →
      ∃ u idx, Codec.Ixon.Univ.WireWF u ∧
        key = Ix.CompileM.univSortKey u ∧
        state.univsIndex.get? u = some idx)
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.internPreseedUnivs univs previous) = .ok ((), state')) :
    (∀ {u idx}, state.univsIndex.get? u = some idx →
      state'.univsIndex.get? u = some idx) ∧
    (∀ entry ∈ univs,
      ∃ idx, state'.univsIndex.get? entry.2 = some idx) := by
  induction univs generalizing previous state state' with
  | nil =>
    simp only [Ix.CompileM.internPreseedUnivs] at hrun
    cases hrun
    refine ⟨fun hget => hget, ?_⟩
    intro entry hmem
    simp at hmem
  | cons entry rest ih =>
    rcases entry with ⟨key, u⟩
    have huWire : Codec.Ixon.Univ.WireWF u := hwire (key, u) (by simp)
    have huKey : key = Ix.CompileM.univSortKey u :=
      hkeys (key, u) (by simp)
    have hrestWire : ∀ value ∈ rest,
        Codec.Ixon.Univ.WireWF value.2 := by
      intro value hmem
      exact hwire value (by simp [hmem])
    have hrestKeys : ∀ value ∈ rest,
        value.1 = Ix.CompileM.univSortKey value.2 := by
      intro value hmem
      exact hkeys value (by simp [hmem])
    cases hnew : previous != some key with
    | false =>
      rw [Ix.CompileM.internPreseedUnivs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      have heq : previous = some key := by simpa using hnew
      obtain ⟨prior, priorIdx, hpriorWire, hpriorKey, hpriorIndex⟩ :=
        hprevious key heq
      have hpriorEq : prior = u :=
        univSortKey_injective_wire hpriorWire huWire
          (hpriorKey.symm.trans huKey)
      subst prior
      have hnextPrevious : ∀ queried, some key = some queried →
          ∃ value idx, Codec.Ixon.Univ.WireWF value ∧
            queried = Ix.CompileM.univSortKey value ∧
            state.univsIndex.get? value = some idx := by
        intro queried hqueried
        cases hqueried
        exact ⟨u, priorIdx, huWire, huKey, hpriorIndex⟩
      obtain ⟨hpreserve, hrest⟩ :=
        ih hrestWire hrestKeys (previous := some key) hnextPrevious hrun
      refine ⟨hpreserve, ?_⟩
      intro queried hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · have hpair : queried = (key, u) := hmem
        subst queried
        exact ⟨priorIdx, hpreserve hpriorIndex⟩
      · exact hrest queried hmem
    | true =>
      let next := (state.internUniv u).1
      rw [Ix.CompileM.internPreseedUnivs, hnew] at hrun
      change Ix.CompileM.CompileM.run compileEnv blockEnv state (do
        discard <| Ix.CompileM.internUniv u
        Ix.CompileM.internPreseedUnivs rest (some key)) =
          .ok ((), state') at hrun
      rw [run_bind, run_discard_internUniv] at hrun
      have hhead : ∃ idx, next.univsIndex.get? u = some idx := by
        let result := state.internUniv u
        refine ⟨result.2, ?_⟩
        exact internUniv_own_index state u
      have hnextPrevious : ∀ queried, some key = some queried →
          ∃ value idx, Codec.Ixon.Univ.WireWF value ∧
            queried = Ix.CompileM.univSortKey value ∧
            next.univsIndex.get? value = some idx := by
        intro queried hqueried
        cases hqueried
        obtain ⟨idx, hidx⟩ := hhead
        exact ⟨u, idx, huWire, huKey, hidx⟩
      obtain ⟨hpreserveNext, hrest⟩ :=
        ih hrestWire hrestKeys (previous := some key) hnextPrevious hrun
      refine ⟨?_, ?_⟩
      · intro queried idx hget
        exact hpreserveNext (internUniv_preserves_index state u queried idx
          hget)
      · intro queried hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · have hpair : queried = (key, u) := hmem
          subst queried
          obtain ⟨idx, hidx⟩ := hhead
          exact ⟨idx, hpreserveNext hidx⟩
        · exact hrest queried hmem

/-- End-to-end singleton preseed execution on the ready ordinary domain.
Collection, sorting, canonicalization, and both commit loops are now
constructed rather than assumed. Capacity and wire conditions are absent
because they govern codec soundness, not termination of these pure state
transitions. -/
theorem preseedExprTables_singleton_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables #[(source, params)]) =
        .ok ((), preseedState) ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  obtain ⟨collected, collectedState, hcollect, hcollectState,
      hcollectWire, hcollectSize⟩ :=
    collectPreseedExprs_singleton_run_ready compileEnv blockEnv state params
      hclosed hfaithful hsource hcanon (#[], #[], {})
      PreseedCollectionWireWF.empty
  rcases collected with ⟨refs, univs, seen⟩
  let sortedRefs := refs.qsort fun a b => a.cmpBytes b == .lt
  obtain ⟨refState, hrefsRun, hrefsExpr, hrefsUniv, hrefsCanon,
      hrefsArena, hrefsUnivs⟩ :=
    internPreseedRefs_run_total compileEnv blockEnv sortedRefs.toList none
      collectedState
  have hrefsCanonWF : CanonUnivCacheWF refState :=
    hcollectState.canonUnivCache.of_cache_eq hrefsCanon
  obtain ⟨canonUnivs, canonState, hcanonRun, hcanonValues,
      hcanonState, hcanonTables, hcanonExpr, hcanonUniv, hcanonArena⟩ :=
    canonPreseedUnivs_run_refines compileEnv blockEnv univs.toList
      (Array.mkEmpty univs.size) hrefsCanonWF
  let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
  let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
    Ix.CompileM.byteArrayCmp ka kb == .lt
  obtain ⟨univState, hunivsRun, hunivsExpr, hunivsUniv, hunivsCanon,
      hunivsArena, hunivsRefs⟩ :=
    internPreseedUnivs_run_total compileEnv blockEnv sortedUnivs.toList none
      canonState
  let preseedState : Ix.CompileM.BlockState :=
    { univState with univsFinal := true }
  have hfinalCanon : CanonUnivCacheWF preseedState := by
    apply CanonUnivCacheWF.of_cache_eq
      (hcanonState.of_cache_eq hunivsCanon)
    rfl
  refine ⟨preseedState, ?_, ?_, hfinalCanon, ?_, rfl⟩
  · unfold Ix.CompileM.preseedExprTables
    rw [run_bind, hcollect]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv collectedState (do
      Ix.CompileM.internPreseedRefs sortedRefs.toList none
      let canonUnivs ← Ix.CompileM.canonPreseedUnivs univs.toList
        (Array.mkEmpty univs.size)
      let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
      let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
        Ix.CompileM.byteArrayCmp ka kb == .lt
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hrefsRun]
    simp only
    rw [run_bind, hcanonRun]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv canonState (do
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hunivsRun]
    rfl
  · change univState.exprCache = state.exprCache
    exact hunivsExpr.trans <| hcanonExpr.trans <| hrefsExpr.trans <|
      hcollectState.exprCache
  · change univState.arena = state.arena
    exact hunivsArena.trans <| hcanonArena.trans <| hrefsArena.trans <|
      hcollectState.arena

/-- End-to-end two-root preseed execution for the common definition/theorem/
opaque shape. Both roots share one universe-parameter context, while
production resets its context-sensitive memo between them. -/
theorem preseedExprTables_pair_run_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {first second : Ix.Expr}
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hsecond : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) second)
    (hcanon : CanonUnivCacheWF state) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables
            #[(first, params), (second, params)]) =
        .ok ((), preseedState) ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  obtain ⟨refs, univs, seen, collectedState, hcollect, hcollectState,
      hcollectWire, hfirstCover, hsecondCover, hcollectSize⟩ :=
    collectPreseedExprs_pair_run_ready_covers compileEnv blockEnv state params
      hclosed hlevelFaithful hexprFaithful hfirst hsecond hcanon
  let sortedRefs := refs.qsort fun a b => a.cmpBytes b == .lt
  obtain ⟨refState, hrefsRun, hrefsExpr, hrefsUniv, hrefsCanon,
      hrefsArena, hrefsUnivs⟩ :=
    internPreseedRefs_run_total compileEnv blockEnv sortedRefs.toList none
      collectedState
  have hrefsCanonWF : CanonUnivCacheWF refState :=
    hcollectState.canonUnivCache.of_cache_eq hrefsCanon
  obtain ⟨canonUnivs, canonState, hcanonRun, hcanonValues,
      hcanonState, hcanonTables, hcanonExpr, hcanonUniv, hcanonArena⟩ :=
    canonPreseedUnivs_run_refines compileEnv blockEnv univs.toList
      (Array.mkEmpty univs.size) hrefsCanonWF
  let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
  let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
    Ix.CompileM.byteArrayCmp ka kb == .lt
  obtain ⟨univState, hunivsRun, hunivsExpr, hunivsUniv, hunivsCanon,
      hunivsArena, hunivsRefs⟩ :=
    internPreseedUnivs_run_total compileEnv blockEnv sortedUnivs.toList none
      canonState
  let preseedState : Ix.CompileM.BlockState :=
    { univState with univsFinal := true }
  have hfinalCanon : CanonUnivCacheWF preseedState := by
    apply CanonUnivCacheWF.of_cache_eq
      (hcanonState.of_cache_eq hunivsCanon)
    rfl
  refine ⟨preseedState, ?_, ?_, hfinalCanon, ?_, rfl⟩
  · unfold Ix.CompileM.preseedExprTables
    rw [run_bind, hcollect]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv collectedState (do
      Ix.CompileM.internPreseedRefs sortedRefs.toList none
      let canonUnivs ← Ix.CompileM.canonPreseedUnivs univs.toList
        (Array.mkEmpty univs.size)
      let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
      let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
        Ix.CompileM.byteArrayCmp ka kb == .lt
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hrefsRun]
    simp only
    rw [run_bind, hcanonRun]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv canonState (do
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hunivsRun]
    rfl
  · change univState.exprCache = state.exprCache
    exact hunivsExpr.trans <| hcanonExpr.trans <| hrefsExpr.trans <|
      hcollectState.exprCache
  · change univState.arena = state.arena
    exact hunivsArena.trans <| hcanonArena.trans <| hrefsArena.trans <|
      hcollectState.arena

/-- Capacity boundary for a singleton collection result. This is phrased
against the proof-visible collection phase, so it constrains table cardinality
without assuming the later preseed transition succeeds. -/
def SingletonPreseedCapacity
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.Expr) (params : List Ix.Name) : Prop :=
  ∀ refs univs seen collectedState,
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectPreseedExprs [(source, params)] (#[], #[], {})) =
      .ok ((refs, univs, seen), collectedState) →
    state.refs.size + refs.size < UInt64.size ∧
      state.univs.size + univs.size < UInt64.size

def SingletonPreseedIndexes
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.Expr) (params : List Ix.Name)
    (preseedState : Ix.CompileM.BlockState) : Prop :=
  ∀ refs univs seen collectedState,
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectPreseedExprs [(source, params)] (#[], #[], {})) =
      .ok ((refs, univs, seen), collectedState) →
    PreseedCollectionIndexed refs univs preseedState

/-- The raw singleton collection contains every reference and universe leaf
needed to compile its source, before sorting, deduplication, or commitment. -/
def SingletonPreseedCovers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.Expr) (params : List Ix.Name) : Prop :=
  ∀ refs univs seen collectedState,
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectPreseedExprs [(source, params)] (#[], #[], {})) =
      .ok ((refs, univs, seen), collectedState) →
    PreseedCollectionCovers compileEnv
      (preseedContextBlockEnv blockEnv params)
      (preseedContextStartState state) refs univs source

/-- Capacity boundary for the two-root singleton preseed used by definition
payloads. -/
def PairPreseedCapacity
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (first second : Ix.Expr) (params : List Ix.Name) : Prop :=
  ∀ refs univs seen collectedState,
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectPreseedExprs
          [(first, params), (second, params)] (#[], #[], {})) =
      .ok ((refs, univs, seen), collectedState) →
    state.refs.size + refs.size < UInt64.size ∧
      state.univs.size + univs.size < UInt64.size

def PairPreseedIndexes
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (first second : Ix.Expr) (params : List Ix.Name)
    (preseedState : Ix.CompileM.BlockState) : Prop :=
  ∀ refs univs seen collectedState,
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectPreseedExprs
          [(first, params), (second, params)] (#[], #[], {})) =
      .ok ((refs, univs, seen), collectedState) →
    PreseedCollectionIndexed refs univs preseedState

def PairPreseedCovers
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (first second : Ix.Expr) (params : List Ix.Name) : Prop :=
  ∀ refs univs seen collectedState,
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.collectPreseedExprs
          [(first, params), (second, params)] (#[], #[], {})) =
      .ok ((refs, univs, seen), collectedState) →
    PreseedCollectionCovers compileEnv
        (preseedContextBlockEnv blockEnv params)
        (preseedContextStartState state) refs univs first ∧
      PreseedCollectionCovers compileEnv
        (preseedContextBlockEnv blockEnv params)
        (preseedContextStartState state) refs univs second

theorem singletonPreseedCovers_of_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state) :
    SingletonPreseedCovers compileEnv blockEnv state source params := by
  obtain ⟨actualRefs, actualUnivs, actualSeen, actualState, hactual,
      hactualState, hactualWire, hactualCovers⟩ :=
    collectPreseedExprs_singleton_run_ready_covers compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful hsource hcanon
  intro refs univs seen collectedState hrun
  rw [hactual] at hrun
  cases hrun
  exact hactualCovers

theorem pairPreseedCovers_of_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {first second : Ix.Expr}
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hsecond : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) second)
    (hcanon : CanonUnivCacheWF state) :
    PairPreseedCovers compileEnv blockEnv state first second params := by
  obtain ⟨actualRefs, actualUnivs, actualSeen, actualState, hactual,
      hactualState, hactualWire, hfirstCovers, hsecondCovers,
      hactualSize⟩ :=
    collectPreseedExprs_pair_run_ready_covers compileEnv blockEnv state params
      hclosed hlevelFaithful hexprFaithful hfirst hsecond hcanon
  intro refs univs seen collectedState hrun
  rw [hactual] at hrun
  cases hrun
  exact ⟨hfirstCovers, hsecondCovers⟩

def SingletonPreseedResolution
    (compileEnv : Ix.CompileM.CompileEnv)
    (state preseedState : Ix.CompileM.BlockState) : Prop :=
  ∀ name, resolveConstAddr? compileEnv preseedState name =
    resolveConstAddr? compileEnv (preseedContextStartState state) name

/-- Pure source-side cardinality bound implying the dynamic collection
capacity boundary. -/
def SingletonPreseedSourceBound (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (source : Ix.Expr) : Prop :=
  state.refs.size + preseedRefCount blockEnv.mutCtx source < UInt64.size ∧
    state.univs.size + preseedUnivCount source < UInt64.size

def PairPreseedSourceBound (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (first second : Ix.Expr) : Prop :=
  state.refs.size +
      (preseedRefCount blockEnv.mutCtx first +
        preseedRefCount blockEnv.mutCtx second) < UInt64.size ∧
    state.univs.size +
      (preseedUnivCount first + preseedUnivCount second) < UInt64.size

def RootPreseedSourceBound (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (sources : List Ix.Expr) : Prop :=
  state.refs.size + preseedRootRefCount blockEnv.mutCtx sources <
      UInt64.size ∧
    state.univs.size + preseedRootUnivCount sources < UInt64.size

def InputPreseedSourceBound (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    (inputs : List (Ix.Expr × List Ix.Name)) : Prop :=
  state.refs.size + preseedInputRefCount blockEnv.mutCtx inputs <
      UInt64.size ∧
    state.univs.size + preseedInputUnivCount inputs < UInt64.size

theorem singletonPreseedCapacity_of_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state)
    (hbound : SingletonPreseedSourceBound blockEnv state source) :
    SingletonPreseedCapacity compileEnv blockEnv state source params := by
  obtain ⟨collected, collectedState, hcollect, hcollectState,
      hcollectWire, hcollectSize⟩ :=
    collectPreseedExprs_singleton_run_ready compileEnv blockEnv state params
      hclosed hfaithful hsource hcanon (#[], #[], {})
      PreseedCollectionWireWF.empty
  rcases collected with ⟨actualRefs, actualUnivs, actualSeen⟩
  intro refs univs seen state' hrun
  rw [hcollect] at hrun
  cases hrun
  have hrefSize := hcollectSize.refs
  have hunivSize := hcollectSize.univs
  simp only [Array.size_empty, Nat.zero_add] at hrefSize hunivSize
  change state.refs.size + preseedRefCount blockEnv.mutCtx source <
      UInt64.size ∧
    state.univs.size + preseedUnivCount source < UInt64.size at hbound
  obtain ⟨hrefBound, hunivBound⟩ := hbound
  exact ⟨by omega, by omega⟩

theorem pairPreseedCapacity_of_ready
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {first second : Ix.Expr}
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hsecond : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) second)
    (hcanon : CanonUnivCacheWF state)
    (hbound : PairPreseedSourceBound blockEnv state first second) :
    PairPreseedCapacity compileEnv blockEnv state first second params := by
  obtain ⟨actualRefs, actualUnivs, actualSeen, actualState, hactual,
      hactualState, hactualWire, hfirstCovers, hsecondCovers,
      hactualSize⟩ :=
    collectPreseedExprs_pair_run_ready_covers compileEnv blockEnv state params
      hclosed hlevelFaithful hexprFaithful hfirst hsecond hcanon
  intro refs univs seen collectedState hrun
  rw [hactual] at hrun
  cases hrun
  obtain ⟨hrefSize, hunivSize⟩ := hactualSize
  change actualRefs.size ≤ preseedRefCount blockEnv.mutCtx first +
    preseedRefCount blockEnv.mutCtx second at hrefSize
  change actualUnivs.size ≤
    preseedUnivCount first + preseedUnivCount second at hunivSize
  obtain ⟨hrefBound, hunivBound⟩ := hbound
  exact ⟨by omega, by omega⟩

/-- Generic wire-safe tail for `preseedExprTables`. Once collection has
produced framed, wire-safe arrays within capacity, sorting, canonicalization,
deduplication, both commits, and finalization establish complete indexes and
preserve name resolution. -/
theorem preseedExprTables_of_collect_run_ready_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state origin : Ix.CompileM.BlockState)
    (exprs : Array (Ix.Expr × List Ix.Name))
    (refs : Array Address) (univs : Array Ixon.Univ)
    (seen : Std.HashMap (Address × Address) Unit)
    (collectedState : Ix.CompileM.BlockState)
    (hcollect : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectPreseedExprs exprs.toList (#[], #[], {})) =
        .ok ((refs, univs, seen), collectedState))
    (hcollectState : PreseedCollectFrameWF origin collectedState)
    (hcollectWire : PreseedCollectionWireWF (refs, univs, seen))
    (hrefs : PreseedRefTableWF origin)
    (hunivs : PreseedUnivTableWF origin)
    (hrefCapacity : origin.refs.size + refs.size < UInt64.size)
    (hunivCapacity : origin.univs.size + univs.size < UInt64.size) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables exprs) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      PreseedCollectionIndexed refs univs preseedState ∧
      (∀ name, resolveConstAddr? compileEnv preseedState name =
        resolveConstAddr? compileEnv origin name) ∧
      preseedState.exprCache = origin.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = origin.arena ∧
      preseedState.univsFinal = true := by
  let sortedRefs := refs.qsort fun a b => a.cmpBytes b == .lt
  have hrefPerm : sortedRefs.toList.Perm refs.toList := by
    dsimp only [sortedRefs]
    exact Array.perm_iff_toList_perm.mp
      (Array.qsort_perm (fun a b : Address => a.cmpBytes b == .lt)
        0 (refs.size - 1) refs)
  have hsortedRefsWire : ∀ addr ∈ sortedRefs.toList,
      addr.hash.size = 32 := by
    intro addr hmem
    apply hcollectWire.refs addr
    have : addr ∈ refs.toList := hrefPerm.mem_iff.mp hmem
    simpa using this
  have hrefsCollected : PreseedRefTableWF collectedState :=
    hrefs.of_exprTableView_eq hcollectState.tables
  have hcollectedRefs : collectedState.refs = origin.refs := by
    exact congrArg ExprTableView.refs hcollectState.tables
  have hrefRoom :
      collectedState.refs.size + sortedRefs.toList.length < UInt64.size := by
    simpa [sortedRefs, hcollectedRefs] using hrefCapacity
  obtain ⟨refState, hrefsRun, hrefsState, hrefsGrowth, hrefsExpr,
      hrefsUniv, hrefsCanon, hrefsArena, hrefsUnivs⟩ :=
    internPreseedRefs_run_wf compileEnv blockEnv sortedRefs.toList none
      hrefsCollected hsortedRefsWire hrefRoom
  obtain ⟨hrefsPreserved, hrefsIndexed⟩ :=
    internPreseedRefs_run_indexed compileEnv blockEnv sortedRefs.toList none
      (by intro addr hnone; simp at hnone) hrefsRun
  have hrefsUnivFrame :=
    internPreseedRefs_run_univTableFrame compileEnv blockEnv
      sortedRefs.toList none hrefsRun
  have hrefsResolutionFrame :=
    internPreseedRefs_run_resolutionFrame compileEnv blockEnv
      sortedRefs.toList none hrefsRun
  have hunivsCollected : PreseedUnivTableWF collectedState :=
    hunivs.of_exprTableView_eq hcollectState.tables
  have hunivsRefState : PreseedUnivTableWF refState :=
    hunivsCollected.of_fields_eq hrefsUnivFrame.1 hrefsUnivFrame.2
  have hrefsCanonWF : CanonUnivCacheWF refState :=
    hcollectState.canonUnivCache.of_cache_eq hrefsCanon
  obtain ⟨canonUnivs, canonState, hcanonRun, hcanonValues,
      hcanonState, hcanonTables, hcanonExpr, hcanonUniv, hcanonArena⟩ :=
    canonPreseedUnivs_run_refines compileEnv blockEnv univs.toList
      (Array.mkEmpty univs.size) hrefsCanonWF
  have hunivsCanonState : PreseedUnivTableWF canonState :=
    hunivsRefState.of_exprTableView_eq hcanonTables
  have hrefsCanonState : PreseedRefTableWF canonState :=
    hrefsState.of_exprTableView_eq hcanonTables
  have hcanonValues' :
      canonUnivs.toList = univs.toList.map Ixon.canonUniv := by
    simpa using hcanonValues
  have hcanonWire : ∀ u ∈ canonUnivs,
      Codec.Ixon.Univ.WireWF u := by
    intro u hmem
    have hmem' : u ∈ canonUnivs.toList := by simpa using hmem
    rw [hcanonValues'] at hmem'
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hmem'
    exact hcollectWire.univs raw (by simpa using hraw)
  let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
  let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
    Ix.CompileM.byteArrayCmp ka kb == .lt
  have hunivPerm : sortedUnivs.toList.Perm keyed.toList := by
    dsimp only [sortedUnivs]
    exact Array.perm_iff_toList_perm.mp
      (Array.qsort_perm
        (fun (a b : ByteArray × Ixon.Univ) =>
          Ix.CompileM.byteArrayCmp a.1 b.1 == .lt)
        0 (keyed.size - 1) keyed)
  have hsortedUnivsWire : ∀ entry ∈ sortedUnivs.toList,
      Codec.Ixon.Univ.WireWF entry.2 := by
    intro entry hmem
    have hkeyed : entry ∈ keyed.toList := hunivPerm.mem_iff.mp hmem
    have hkeyed' : entry ∈ canonUnivs.toList.map
        (fun u => (Ix.CompileM.univSortKey u, u)) := by
      simpa [keyed] using hkeyed
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hkeyed'
    exact hcanonWire u (by simpa using hu)
  have hsortedUnivsKeys : ∀ entry ∈ sortedUnivs.toList,
      entry.1 = Ix.CompileM.univSortKey entry.2 := by
    intro entry hmem
    have hkeyed : entry ∈ keyed.toList := hunivPerm.mem_iff.mp hmem
    have hkeyed' : entry ∈ canonUnivs.toList.map
        (fun u => (Ix.CompileM.univSortKey u, u)) := by
      simpa [keyed] using hkeyed
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hkeyed'
    rfl
  have hcanonSize : canonUnivs.size = univs.size := by
    have h := congrArg List.length hcanonValues'
    simpa using h
  have hcollectedUnivs : collectedState.univs = origin.univs := by
    exact congrArg ExprTableView.univs hcollectState.tables
  have hcanonPrimary : canonState.univs.size = origin.univs.size := by
    have hcanonPrimary := congrArg ExprTableView.univs hcanonTables
    change canonState.univs = refState.univs at hcanonPrimary
    rw [hcanonPrimary, hrefsUnivFrame.1, hcollectedUnivs]
  have hsortedUnivsLength : sortedUnivs.toList.length = univs.size := by
    simp [sortedUnivs, keyed, hcanonSize]
  have hunivRoom :
      canonState.univs.size + sortedUnivs.toList.length < UInt64.size := by
    omega
  obtain ⟨univState, hunivsRun, hunivsState, hunivsGrowth, hunivsExpr,
      hunivsUniv, hunivsCanon, hunivsArena, hunivsRefs⟩ :=
    internPreseedUnivs_run_wf compileEnv blockEnv sortedUnivs.toList none
      hunivsCanonState hsortedUnivsWire hunivRoom
  obtain ⟨hunivsPreserved, hunivsIndexed⟩ :=
    internPreseedUnivs_run_indexed compileEnv blockEnv sortedUnivs.toList
      none hsortedUnivsWire hsortedUnivsKeys
      (by intro key hnone; simp at hnone) hunivsRun
  have hunivsRefFrame :=
    internPreseedUnivs_run_refTableFrame compileEnv blockEnv
      sortedUnivs.toList none hunivsRun
  have hunivsResolutionFrame :=
    internPreseedUnivs_run_resolutionFrame compileEnv blockEnv
      sortedUnivs.toList none hunivsRun
  have hrefsUnivState : PreseedRefTableWF univState :=
    hrefsCanonState.of_fields_eq hunivsRefFrame.1 hunivsRefFrame.2
  let preseedState : Ix.CompileM.BlockState :=
    { univState with univsFinal := true }
  have hfinalRefs : PreseedRefTableWF preseedState := by
    exact hrefsUnivState.of_fields_eq rfl rfl
  have hfinalUnivs : PreseedUnivTableWF preseedState := by
    exact hunivsState.of_fields_eq rfl rfl
  have hfinalTables : BlockWireTablesWF preseedState :=
    BlockWireTablesWF.of_preseed hfinalRefs hfinalUnivs
  have hcanonRefsIndex : canonState.refsIndex = refState.refsIndex :=
    congrArg ExprTableView.refsIndex hcanonTables
  have hactualIndexes : PreseedCollectionIndexed refs univs preseedState := by
    constructor
    · intro addr hmem
      have hmemList : addr ∈ refs.toList := by simpa using hmem
      have hsorted : addr ∈ sortedRefs.toList :=
        hrefPerm.mem_iff.mpr hmemList
      obtain ⟨idx, hidx⟩ := hrefsIndexed addr hsorted
      refine ⟨idx, ?_⟩
      change univState.refsIndex.get? addr = some idx
      rw [hunivsRefFrame.2, hcanonRefsIndex]
      exact hidx
    · intro raw hmem
      have hrawList : raw ∈ univs.toList := by simpa using hmem
      have hcanonList : Ixon.canonUniv raw ∈ canonUnivs.toList := by
        rw [hcanonValues']
        exact List.mem_map.mpr ⟨raw, hrawList, rfl⟩
      have hkeyed :
          (Ix.CompileM.univSortKey (Ixon.canonUniv raw),
            Ixon.canonUniv raw) ∈ keyed.toList := by
        simpa [keyed] using hcanonList
      have hsorted :
          (Ix.CompileM.univSortKey (Ixon.canonUniv raw),
            Ixon.canonUniv raw) ∈ sortedUnivs.toList :=
        hunivPerm.mem_iff.mpr hkeyed
      obtain ⟨idx, hidx⟩ := hunivsIndexed _ hsorted
      exact ⟨idx, hidx⟩
  have hcanonBlockName :
      canonState.blockNameToAddr = refState.blockNameToAddr := by
    exact congrArg ExprTableView.blockNameToAddr hcanonTables
  have hcanonAuxName : canonState.auxNameToAddr = refState.auxNameToAddr := by
    exact congrArg ExprTableView.auxNameToAddr hcanonTables
  have hcollectBlockName :
      collectedState.blockNameToAddr = origin.blockNameToAddr := by
    exact congrArg ExprTableView.blockNameToAddr hcollectState.tables
  have hcollectAuxName :
      collectedState.auxNameToAddr = origin.auxNameToAddr := by
    exact congrArg ExprTableView.auxNameToAddr hcollectState.tables
  have hfinalResolution : ∀ name,
      resolveConstAddr? compileEnv preseedState name =
        resolveConstAddr? compileEnv origin name := by
    intro name
    unfold resolveConstAddr?
    rw [hunivsResolutionFrame.1, hcanonBlockName,
      hrefsResolutionFrame.1, hcollectBlockName,
      hunivsResolutionFrame.2, hcanonAuxName,
      hrefsResolutionFrame.2, hcollectAuxName]
  have hfinalCanon : CanonUnivCacheWF preseedState := by
    apply CanonUnivCacheWF.of_cache_eq
      (hcanonState.of_cache_eq hunivsCanon)
    rfl
  refine ⟨preseedState, ?_, hfinalTables, hactualIndexes,
    hfinalResolution, ?_, hfinalCanon, ?_, rfl⟩
  · unfold Ix.CompileM.preseedExprTables
    rw [run_bind, hcollect]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv collectedState (do
      Ix.CompileM.internPreseedRefs sortedRefs.toList none
      let canonUnivs ← Ix.CompileM.canonPreseedUnivs univs.toList
        (Array.mkEmpty univs.size)
      let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
      let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
        Ix.CompileM.byteArrayCmp ka kb == .lt
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hrefsRun]
    simp only
    rw [run_bind, hcanonRun]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv canonState (do
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hunivsRun]
    rfl
  · change univState.exprCache = origin.exprCache
    exact hunivsExpr.trans <| hcanonExpr.trans <| hrefsExpr.trans <|
      hcollectState.exprCache
  · change univState.arena = origin.arena
    exact hunivsArena.trans <| hcanonArena.trans <| hrefsArena.trans <|
      hcollectState.arena

/-- The constructed singleton preseed run produces wire-safe primary tables
when its initial tables are sound and its collected cardinalities fit the
wire. This discharges payload safety and both commit invariants independently
of source-leaf reference coverage. -/
theorem preseedExprTables_singleton_run_ready_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hfaithful : LevelKeyFaithfulOn levelSupport)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hcapacity : SingletonPreseedCapacity compileEnv blockEnv state
      source params) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables #[(source, params)]) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      SingletonPreseedIndexes compileEnv blockEnv state source params
        preseedState ∧
      SingletonPreseedResolution compileEnv state preseedState ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  obtain ⟨collected, collectedState, hcollect, hcollectState,
      hcollectWire, hcollectSize⟩ :=
    collectPreseedExprs_singleton_run_ready compileEnv blockEnv state params
      hclosed hfaithful hsource hcanon (#[], #[], {})
      PreseedCollectionWireWF.empty
  rcases collected with ⟨refs, univs, seen⟩
  obtain ⟨hrefCapacity, hunivCapacity⟩ :=
    hcapacity refs univs seen collectedState hcollect
  let sortedRefs := refs.qsort fun a b => a.cmpBytes b == .lt
  have hrefPerm : sortedRefs.toList.Perm refs.toList := by
    dsimp only [sortedRefs]
    exact Array.perm_iff_toList_perm.mp
      (Array.qsort_perm (fun a b : Address => a.cmpBytes b == .lt)
        0 (refs.size - 1) refs)
  have hsortedRefsWire : ∀ addr ∈ sortedRefs.toList,
      addr.hash.size = 32 := by
    intro addr hmem
    apply hcollectWire.refs addr
    have : addr ∈ refs.toList := hrefPerm.mem_iff.mp hmem
    simpa using this
  have hrefsStart :
      PreseedRefTableWF (preseedContextStartState state) := by
    exact hrefs.of_fields_eq rfl rfl
  have hrefsCollected : PreseedRefTableWF collectedState :=
    hrefsStart.of_exprTableView_eq hcollectState.tables
  have hcollectedRefs : collectedState.refs = state.refs := by
    have h := congrArg ExprTableView.refs hcollectState.tables
    exact h
  have hrefRoom :
      collectedState.refs.size + sortedRefs.toList.length < UInt64.size := by
    simpa [sortedRefs, hcollectedRefs] using hrefCapacity
  obtain ⟨refState, hrefsRun, hrefsState, hrefsGrowth, hrefsExpr,
      hrefsUniv, hrefsCanon, hrefsArena, hrefsUnivs⟩ :=
    internPreseedRefs_run_wf compileEnv blockEnv sortedRefs.toList none
      hrefsCollected hsortedRefsWire hrefRoom
  obtain ⟨hrefsPreserved, hrefsIndexed⟩ :=
    internPreseedRefs_run_indexed compileEnv blockEnv sortedRefs.toList none
      (by intro addr hnone; simp at hnone) hrefsRun
  have hrefsUnivFrame :=
    internPreseedRefs_run_univTableFrame compileEnv blockEnv
      sortedRefs.toList none hrefsRun
  have hrefsResolutionFrame :=
    internPreseedRefs_run_resolutionFrame compileEnv blockEnv
      sortedRefs.toList none hrefsRun
  have hunivsStart :
      PreseedUnivTableWF (preseedContextStartState state) := by
    exact hunivs.of_fields_eq rfl rfl
  have hunivsCollected : PreseedUnivTableWF collectedState :=
    hunivsStart.of_exprTableView_eq hcollectState.tables
  have hunivsRefState : PreseedUnivTableWF refState :=
    hunivsCollected.of_fields_eq hrefsUnivFrame.1 hrefsUnivFrame.2
  have hrefsCanonWF : CanonUnivCacheWF refState :=
    hcollectState.canonUnivCache.of_cache_eq hrefsCanon
  obtain ⟨canonUnivs, canonState, hcanonRun, hcanonValues,
      hcanonState, hcanonTables, hcanonExpr, hcanonUniv, hcanonArena⟩ :=
    canonPreseedUnivs_run_refines compileEnv blockEnv univs.toList
      (Array.mkEmpty univs.size) hrefsCanonWF
  have hunivsCanonState : PreseedUnivTableWF canonState :=
    hunivsRefState.of_exprTableView_eq hcanonTables
  have hrefsCanonState : PreseedRefTableWF canonState :=
    hrefsState.of_exprTableView_eq hcanonTables
  have hcanonValues' :
      canonUnivs.toList = univs.toList.map Ixon.canonUniv := by
    simpa using hcanonValues
  have hcanonWire : ∀ u ∈ canonUnivs,
      Codec.Ixon.Univ.WireWF u := by
    intro u hmem
    have hmem' : u ∈ canonUnivs.toList := by simpa using hmem
    rw [hcanonValues'] at hmem'
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hmem'
    exact hcollectWire.univs raw (by simpa using hraw)
  let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
  let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
    Ix.CompileM.byteArrayCmp ka kb == .lt
  have hunivPerm : sortedUnivs.toList.Perm keyed.toList := by
    dsimp only [sortedUnivs]
    exact Array.perm_iff_toList_perm.mp
      (Array.qsort_perm
        (fun (a b : ByteArray × Ixon.Univ) =>
          Ix.CompileM.byteArrayCmp a.1 b.1 == .lt)
        0 (keyed.size - 1) keyed)
  have hsortedUnivsWire : ∀ entry ∈ sortedUnivs.toList,
      Codec.Ixon.Univ.WireWF entry.2 := by
    intro entry hmem
    have hkeyed : entry ∈ keyed.toList := hunivPerm.mem_iff.mp hmem
    have hkeyed' : entry ∈ canonUnivs.toList.map
        (fun u => (Ix.CompileM.univSortKey u, u)) := by
      simpa [keyed] using hkeyed
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hkeyed'
    exact hcanonWire u (by simpa using hu)
  have hsortedUnivsKeys : ∀ entry ∈ sortedUnivs.toList,
      entry.1 = Ix.CompileM.univSortKey entry.2 := by
    intro entry hmem
    have hkeyed : entry ∈ keyed.toList := hunivPerm.mem_iff.mp hmem
    have hkeyed' : entry ∈ canonUnivs.toList.map
        (fun u => (Ix.CompileM.univSortKey u, u)) := by
      simpa [keyed] using hkeyed
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hkeyed'
    rfl
  have hcanonSize : canonUnivs.size = univs.size := by
    have h := congrArg List.length hcanonValues'
    simpa using h
  have hcollectedUnivs : collectedState.univs = state.univs := by
    have h := congrArg ExprTableView.univs hcollectState.tables
    exact h
  have hcanonPrimary : canonState.univs.size = state.univs.size := by
    have hcanonPrimary := congrArg ExprTableView.univs hcanonTables
    change canonState.univs = refState.univs at hcanonPrimary
    rw [hcanonPrimary, hrefsUnivFrame.1, hcollectedUnivs]
  have hsortedUnivsLength : sortedUnivs.toList.length = univs.size := by
    simp [sortedUnivs, keyed, hcanonSize]
  have hunivRoom :
      canonState.univs.size + sortedUnivs.toList.length < UInt64.size := by
    omega
  obtain ⟨univState, hunivsRun, hunivsState, hunivsGrowth, hunivsExpr,
      hunivsUniv, hunivsCanon, hunivsArena, hunivsRefs⟩ :=
    internPreseedUnivs_run_wf compileEnv blockEnv sortedUnivs.toList none
      hunivsCanonState hsortedUnivsWire hunivRoom
  obtain ⟨hunivsPreserved, hunivsIndexed⟩ :=
    internPreseedUnivs_run_indexed compileEnv blockEnv sortedUnivs.toList
      none hsortedUnivsWire hsortedUnivsKeys
      (by intro key hnone; simp at hnone) hunivsRun
  have hunivsRefFrame :=
    internPreseedUnivs_run_refTableFrame compileEnv blockEnv
      sortedUnivs.toList none hunivsRun
  have hunivsResolutionFrame :=
    internPreseedUnivs_run_resolutionFrame compileEnv blockEnv
      sortedUnivs.toList none hunivsRun
  have hrefsUnivState : PreseedRefTableWF univState :=
    hrefsCanonState.of_fields_eq hunivsRefFrame.1 hunivsRefFrame.2
  let preseedState : Ix.CompileM.BlockState :=
    { univState with univsFinal := true }
  have hfinalRefs : PreseedRefTableWF preseedState := by
    exact hrefsUnivState.of_fields_eq rfl rfl
  have hfinalUnivs : PreseedUnivTableWF preseedState := by
    exact hunivsState.of_fields_eq rfl rfl
  have hfinalTables : BlockWireTablesWF preseedState :=
    BlockWireTablesWF.of_preseed hfinalRefs hfinalUnivs
  have hcanonRefsIndex : canonState.refsIndex = refState.refsIndex :=
    congrArg ExprTableView.refsIndex hcanonTables
  have hactualIndexes : PreseedCollectionIndexed refs univs preseedState := by
    constructor
    · intro addr hmem
      have hmemList : addr ∈ refs.toList := by simpa using hmem
      have hsorted : addr ∈ sortedRefs.toList :=
        hrefPerm.mem_iff.mpr hmemList
      obtain ⟨idx, hidx⟩ := hrefsIndexed addr hsorted
      refine ⟨idx, ?_⟩
      change univState.refsIndex.get? addr = some idx
      rw [hunivsRefFrame.2, hcanonRefsIndex]
      exact hidx
    · intro raw hmem
      have hrawList : raw ∈ univs.toList := by simpa using hmem
      have hcanonList : Ixon.canonUniv raw ∈ canonUnivs.toList := by
        rw [hcanonValues']
        exact List.mem_map.mpr ⟨raw, hrawList, rfl⟩
      have hkeyed :
          (Ix.CompileM.univSortKey (Ixon.canonUniv raw),
            Ixon.canonUniv raw) ∈ keyed.toList := by
        simpa [keyed] using hcanonList
      have hsorted :
          (Ix.CompileM.univSortKey (Ixon.canonUniv raw),
            Ixon.canonUniv raw) ∈ sortedUnivs.toList :=
        hunivPerm.mem_iff.mpr hkeyed
      obtain ⟨idx, hidx⟩ := hunivsIndexed _ hsorted
      exact ⟨idx, hidx⟩
  have hfinalIndexes : SingletonPreseedIndexes compileEnv blockEnv state
      source params preseedState := by
    intro refs' univs' seen' collectedState' hrun
    rw [hcollect] at hrun
    cases hrun
    exact hactualIndexes
  have hcanonBlockName :
      canonState.blockNameToAddr = refState.blockNameToAddr := by
    exact congrArg ExprTableView.blockNameToAddr hcanonTables
  have hcanonAuxName : canonState.auxNameToAddr = refState.auxNameToAddr := by
    exact congrArg ExprTableView.auxNameToAddr hcanonTables
  have hcollectBlockName :
      collectedState.blockNameToAddr =
        (preseedContextStartState state).blockNameToAddr := by
    exact congrArg ExprTableView.blockNameToAddr hcollectState.tables
  have hcollectAuxName :
      collectedState.auxNameToAddr =
        (preseedContextStartState state).auxNameToAddr := by
    exact congrArg ExprTableView.auxNameToAddr hcollectState.tables
  have hfinalResolution :
      SingletonPreseedResolution compileEnv state preseedState := by
    intro name
    unfold resolveConstAddr?
    rw [hunivsResolutionFrame.1, hcanonBlockName,
      hrefsResolutionFrame.1, hcollectBlockName,
      hunivsResolutionFrame.2, hcanonAuxName,
      hrefsResolutionFrame.2, hcollectAuxName]
  have hfinalCanon : CanonUnivCacheWF preseedState := by
    apply CanonUnivCacheWF.of_cache_eq
      (hcanonState.of_cache_eq hunivsCanon)
    rfl
  refine ⟨preseedState, ?_, hfinalTables, hfinalIndexes, hfinalResolution,
    ?_, hfinalCanon, ?_, rfl⟩
  · unfold Ix.CompileM.preseedExprTables
    rw [run_bind, hcollect]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv collectedState (do
      Ix.CompileM.internPreseedRefs sortedRefs.toList none
      let canonUnivs ← Ix.CompileM.canonPreseedUnivs univs.toList
        (Array.mkEmpty univs.size)
      let keyed := canonUnivs.map fun u => (Ix.CompileM.univSortKey u, u)
      let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
        Ix.CompileM.byteArrayCmp ka kb == .lt
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hrefsRun]
    simp only
    rw [run_bind, hcanonRun]
    simp only
    change Ix.CompileM.CompileM.run compileEnv blockEnv canonState (do
      Ix.CompileM.internPreseedUnivs sortedUnivs.toList none
      Ix.CompileM.modifyBlockState fun current =>
        { current with univsFinal := true }) = _
    rw [run_bind, hunivsRun]
    rfl
  · change univState.exprCache = state.exprCache
    exact hunivsExpr.trans <| hcanonExpr.trans <| hrefsExpr.trans <|
      hcollectState.exprCache
  · change univState.arena = state.arena
    exact hunivsArena.trans <| hcanonArena.trans <| hrefsArena.trans <|
      hcollectState.arena

/-- Source readiness and a structural singleton bound construct the one-root
preseed and its frozen reference compilation. -/
theorem preseedExprTables_singleton_run_ready_frozenRef
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {source : Ix.Expr}
    (hsource : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hbound : SingletonPreseedSourceBound blockEnv state source) :
    ∃ preseedState target,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables #[(source, params)]) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      compileExprRef
          (frozenRefCompileCtx compileEnv
            (preseedContextBlockEnv blockEnv params) preseedState)
          source = some target ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  have hcapacity : SingletonPreseedCapacity compileEnv blockEnv state
      source params :=
    singletonPreseedCapacity_of_ready compileEnv blockEnv state params
      hclosed hlevelFaithful hsource hcanon hbound
  obtain ⟨preseedState, hpreseed, htables, hindexes, hresolution,
      hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_singleton_run_ready_wireWF compileEnv blockEnv state
      params hclosed hlevelFaithful hsource hcanon hrefs hunivs hcapacity
  obtain ⟨refs, univs, seen, collectedState, hcollect, hcollectState,
      hcollectWire, hcovers⟩ :=
    collectPreseedExprs_singleton_run_ready_covers compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful hsource hcanon
  have hindexed := hindexes refs univs seen collectedState hcollect
  obtain ⟨target, htarget⟩ :=
    hcovers.compileExprRef_of_indexed hindexed hresolution
  exact ⟨preseedState, target, hpreseed, htables, htarget, hexpr,
    hcanonState, harena, hfinal⟩

/-- The two-root production preseed constructs wire-safe tables and complete
indexes for the shared raw collection. -/
theorem preseedExprTables_pair_run_ready_wireWF
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {first second : Ix.Expr}
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hsecond : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) second)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hcapacity : PairPreseedCapacity compileEnv blockEnv state
      first second params) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables
            #[(first, params), (second, params)]) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      PairPreseedIndexes compileEnv blockEnv state first second params
        preseedState ∧
      SingletonPreseedResolution compileEnv state preseedState ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  let contextEnv := preseedContextBlockEnv blockEnv params
  let origin := preseedContextStartState state
  obtain ⟨refs, univs, seen, collectedState, hcollect, hcollectState,
      hcollectWire, hfirstCover, hsecondCover, hcollectSize⟩ :=
    collectPreseedExprs_pair_run_ready_covers compileEnv blockEnv state params
      hclosed hlevelFaithful hexprFaithful hfirst hsecond hcanon
  obtain ⟨hrefCapacity, hunivCapacity⟩ :=
    hcapacity refs univs seen collectedState hcollect
  have hrefsOrigin : PreseedRefTableWF origin := by
    exact hrefs.of_fields_eq rfl rfl
  have hunivsOrigin : PreseedUnivTableWF origin := by
    exact hunivs.of_fields_eq rfl rfl
  have hrefCapacity' : origin.refs.size + refs.size < UInt64.size := by
    simpa [origin, preseedContextStartState] using hrefCapacity
  have hunivCapacity' : origin.univs.size + univs.size < UInt64.size := by
    simpa [origin, preseedContextStartState] using hunivCapacity
  obtain ⟨preseedState, hpreseed, htables, hindexed, hresolution,
      hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_of_collect_run_ready_wireWF compileEnv blockEnv
      state origin #[(first, params), (second, params)] refs univs
      seen collectedState hcollect hcollectState.frame hcollectWire hrefsOrigin
      hunivsOrigin hrefCapacity' hunivCapacity'
  have hfinalIndexes : PairPreseedIndexes compileEnv blockEnv state
      first second params preseedState := by
    intro refs' univs' seen' collectedState' hrun
    rw [hcollect] at hrun
    cases hrun
    exact hindexed
  have hfinalResolution :
      SingletonPreseedResolution compileEnv state preseedState := by
    exact hresolution
  refine ⟨preseedState, hpreseed, htables, hfinalIndexes,
    hfinalResolution, ?_, hcanonState, ?_, hfinal⟩
  · simpa [origin, preseedContextStartState] using hexpr
  · simpa [origin, preseedContextStartState] using harena

/-- Source readiness and a structural pair bound construct the two-root
preseed and both frozen reference compilations needed by the definition-like
singleton drivers. -/
theorem preseedExprTables_pair_run_ready_frozenRefs
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    {first second : Ix.Expr}
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hsecond : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) second)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hbound : PairPreseedSourceBound blockEnv state first second) :
    ∃ preseedState firstTarget secondTarget,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables
            #[(first, params), (second, params)]) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      compileExprRef
          (frozenRefCompileCtx compileEnv
            (preseedContextBlockEnv blockEnv params) preseedState)
          first = some firstTarget ∧
      compileExprRef
          (frozenRefCompileCtx compileEnv
            (preseedContextBlockEnv blockEnv params) preseedState)
          second = some secondTarget ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  have hcapacity : PairPreseedCapacity compileEnv blockEnv state
      first second params :=
    pairPreseedCapacity_of_ready compileEnv blockEnv state params hclosed
      hlevelFaithful hexprFaithful hfirst hsecond hcanon hbound
  obtain ⟨preseedState, hpreseed, htables, hindexes, hresolution,
      hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_pair_run_ready_wireWF compileEnv blockEnv state params
      hclosed hlevelFaithful hexprFaithful hfirst hsecond hcanon hrefs hunivs
      hcapacity
  obtain ⟨refs, univs, seen, collectedState, hcollect, hcollectState,
      hcollectWire, hfirstCover, hsecondCover, hcollectSize⟩ :=
    collectPreseedExprs_pair_run_ready_covers compileEnv blockEnv state params
      hclosed hlevelFaithful hexprFaithful hfirst hsecond hcanon
  have hindexed := hindexes refs univs seen collectedState hcollect
  obtain ⟨firstTarget, hfirstTarget⟩ :=
    hfirstCover.compileExprRef_of_indexed hindexed hresolution
  obtain ⟨secondTarget, hsecondTarget⟩ :=
    hsecondCover.compileExprRef_of_indexed hindexed hresolution
  exact ⟨preseedState, firstTarget, secondTarget, hpreseed, htables,
    hfirstTarget, hsecondTarget, hexpr, hcanonState, harena, hfinal⟩

/-- A nonempty same-context root list gets one production preseed run and a
frozen reference target for every source. This is the shared preseed interface
for standalone recursors and inductive constructor families. -/
theorem preseedExprTables_roots_run_ready_frozenRefs
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (first : Ix.Expr) (rest : List Ix.Expr)
    (hfirst : PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) first)
    (hrest : ∀ source ∈ rest, PreseedReady compileEnv
      (preseedContextBlockEnv blockEnv params) levelSupport
      (preseedContextStartState state) source)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hbound : RootPreseedSourceBound blockEnv state (first :: rest)) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables
            (((first :: rest).map fun source => (source, params)).toArray)) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      (∀ source ∈ first :: rest, ∃ target,
        compileExprRef
          (frozenRefCompileCtx compileEnv
            (preseedContextBlockEnv blockEnv params) preseedState)
          source = some target) ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  let contextEnv := preseedContextBlockEnv blockEnv params
  let origin := preseedContextStartState state
  let exprs :=
    (((first :: rest).map fun source => (source, params)).toArray)
  obtain ⟨refs, univs, seen, collectedState, hcollect, hcollectState,
      hcollectWire, hcovers, hcollectSize⟩ :=
    collectPreseedExprs_roots_run_ready_covers compileEnv blockEnv state
      params hclosed hlevelFaithful hexprFaithful first rest hfirst hrest
      hcanon
  have hcollect' : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectPreseedExprs exprs.toList (#[], #[], {})) =
        .ok ((refs, univs, seen), collectedState) := by
    simpa [exprs] using hcollect
  have hrefsOrigin : PreseedRefTableWF origin := by
    exact hrefs.of_fields_eq rfl rfl
  have hunivsOrigin : PreseedUnivTableWF origin := by
    exact hunivs.of_fields_eq rfl rfl
  have hrefSize : refs.size ≤
      preseedRootRefCount blockEnv.mutCtx (first :: rest) := by
    simpa using hcollectSize.refs
  have hunivSize : univs.size ≤
      preseedRootUnivCount (first :: rest) := by
    simpa using hcollectSize.univs
  obtain ⟨hrefBound, hunivBound⟩ := hbound
  have hrefCapacity : origin.refs.size + refs.size < UInt64.size := by
    dsimp only [origin, preseedContextStartState]
    omega
  have hunivCapacity : origin.univs.size + univs.size < UInt64.size := by
    dsimp only [origin, preseedContextStartState]
    omega
  obtain ⟨preseedState, hpreseed, htables, hindexed, hresolution,
      hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_of_collect_run_ready_wireWF compileEnv blockEnv
      state origin exprs refs univs seen collectedState hcollect'
      hcollectState.frame hcollectWire hrefsOrigin hunivsOrigin hrefCapacity
      hunivCapacity
  have htargets : ∀ source ∈ first :: rest, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv contextEnv preseedState)
        source = some target := by
    intro source hmem
    exact (hcovers source hmem).compileExprRef_of_indexed
      hindexed hresolution
  refine ⟨preseedState, ?_, htables, htargets, ?_, hcanonState, ?_,
    hfinal⟩
  · simpa [exprs] using hpreseed
  · simpa [origin, preseedContextStartState] using hexpr
  · simpa [origin, preseedContextStartState] using harena

/-- A heterogeneous production preseed run commits one frozen table snapshot
and recovers a reference-compiled target for every source under that source's
own universe-parameter context. The explicit seen-set discipline is the sole
additional boundary beyond the same source, hash-faithfulness, and capacity
conditions used by homogeneous root lists. -/
theorem preseedExprTables_inputs_run_ready_frozenRefs
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inputs : List (Ix.Expr × List Ix.Name))
    (hready : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv input.2) levelSupport
        (preseedContextStartState state) input.1)
    (hseen : HeterogeneousPreseedSeenSafe compileEnv blockEnv
      (preseedContextStartState state) inputs (#[], #[], {}) state)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hbound : InputPreseedSourceBound blockEnv state inputs) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables inputs.toArray) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      (∀ input ∈ inputs, ∃ target,
        compileExprRef
          (frozenRefCompileCtx compileEnv
            (preseedContextBlockEnv blockEnv input.2) preseedState)
          input.1 = some target) ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  let origin := preseedContextStartState state
  obtain ⟨refs, univs, seen, collectedState, hcollect, hcollectState,
      hcollectWire, hcovers, hcollectSize⟩ :=
    collectPreseedExprs_inputs_run_ready_covers compileEnv blockEnv state
      hclosed hlevelFaithful hexprFaithful inputs hready hcanon hseen
  have hcollect' : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectPreseedExprs inputs.toArray.toList
        (#[], #[], {})) =
        .ok ((refs, univs, seen), collectedState) := by
    simpa using hcollect
  have hrefsOrigin : PreseedRefTableWF origin := by
    exact hrefs.of_fields_eq rfl rfl
  have hunivsOrigin : PreseedUnivTableWF origin := by
    exact hunivs.of_fields_eq rfl rfl
  have hrefSize : refs.size ≤
      preseedInputRefCount blockEnv.mutCtx inputs := by
    simpa using hcollectSize.refs
  have hunivSize : univs.size ≤ preseedInputUnivCount inputs := by
    simpa using hcollectSize.univs
  obtain ⟨hrefBound, hunivBound⟩ := hbound
  have hrefCapacity : origin.refs.size + refs.size < UInt64.size := by
    dsimp only [origin, preseedContextStartState]
    omega
  have hunivCapacity : origin.univs.size + univs.size < UInt64.size := by
    dsimp only [origin, preseedContextStartState]
    omega
  obtain ⟨preseedState, hpreseed, htables, hindexed, hresolution,
      hexpr, hcanonState, harena, hfinal⟩ :=
    preseedExprTables_of_collect_run_ready_wireWF compileEnv blockEnv state
      origin inputs.toArray refs univs seen collectedState hcollect'
      hcollectState hcollectWire hrefsOrigin hunivsOrigin hrefCapacity
      hunivCapacity
  have htargets : ∀ input ∈ inputs, ∃ target,
      compileExprRef
        (frozenRefCompileCtx compileEnv
          (preseedContextBlockEnv blockEnv input.2) preseedState)
        input.1 = some target := by
    intro input hmem
    exact (hcovers input hmem).compileExprRef_of_indexed
      hindexed hresolution
  refine ⟨preseedState, ?_, htables, htargets, ?_, hcanonState, ?_,
    hfinal⟩
  · simpa using hpreseed
  · simpa [origin, preseedContextStartState] using hexpr
  · simpa [origin, preseedContextStartState] using harena

/-- Frozen heterogeneous preseeding without a caller-supplied seen-set
invariant when every input carries the same universe-parameter context. -/
theorem preseedExprTables_inputs_run_uniform_ready_frozenRefs
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (state : Ix.CompileM.BlockState) (params : List Ix.Name)
    {levelSupport : Ix.Level → Prop}
    (hclosed : LevelSupportClosed levelSupport)
    (hlevelFaithful : LevelKeyFaithfulOn levelSupport)
    (hexprFaithful : ExprKeyFaithfulOn OrdinaryExpr)
    (inputs : List (Ix.Expr × List Ix.Name))
    (hparams : ∀ input ∈ inputs, input.2 = params)
    (hready : ∀ input ∈ inputs,
      PreseedReady compileEnv
        (preseedContextBlockEnv blockEnv input.2) levelSupport
        (preseedContextStartState state) input.1)
    (hcanon : CanonUnivCacheWF state)
    (hrefs : PreseedRefTableWF state)
    (hunivs : PreseedUnivTableWF state)
    (hbound : InputPreseedSourceBound blockEnv state inputs) :
    ∃ preseedState,
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.preseedExprTables inputs.toArray) =
        .ok ((), preseedState) ∧
      BlockWireTablesWF preseedState ∧
      (∀ input ∈ inputs, ∃ target,
        compileExprRef
          (frozenRefCompileCtx compileEnv
            (preseedContextBlockEnv blockEnv input.2) preseedState)
          input.1 = some target) ∧
      preseedState.exprCache = state.exprCache ∧
      CanonUnivCacheWF preseedState ∧
      preseedState.arena = state.arena ∧
      preseedState.univsFinal = true := by
  have hseen := heterogeneousPreseedSeenSafe_of_uniform compileEnv blockEnv
    state params hclosed hlevelFaithful hexprFaithful inputs hparams hready
    hcanon
  exact preseedExprTables_inputs_run_ready_frozenRefs compileEnv blockEnv
    state hclosed hlevelFaithful hexprFaithful inputs hready hseen hcanon
    hrefs hunivs hbound

/-- Every successful preseed pass marks the primary universe table final.
This postcondition is independent of how many roots or table entries were
collected. -/
theorem preseedExprTables_run_univsFinal
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (exprs : Array (Ix.Expr × List Ix.Name))
    {state' : Ix.CompileM.BlockState}
    (hrun : Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.preseedExprTables exprs) = .ok ((), state')) :
    state'.univsFinal = true := by
  unfold Ix.CompileM.preseedExprTables at hrun
  rw [run_bind] at hrun
  generalize Ix.CompileM.CompileM.run compileEnv blockEnv state
      (Ix.CompileM.collectPreseedExprs exprs.toList (#[], #[], {})) =
    collectedResult at hrun
  cases collectedResult with
  | error err => simp at hrun
  | ok collectedState =>
    rcases collectedState with ⟨collected, collectedState⟩
    rcases collected with ⟨refs, univs, seen⟩
    simp only at hrun
    rw [run_bind] at hrun
    generalize Ix.CompileM.CompileM.run compileEnv blockEnv collectedState
        (Ix.CompileM.internPreseedRefs
          (refs.qsort fun a b => a.cmpBytes b == .lt).toList none) =
      refsResult at hrun
    cases refsResult with
    | error err => simp at hrun
    | ok refState =>
      rcases refState with ⟨_, refState⟩
      simp only at hrun
      rw [run_bind] at hrun
      generalize Ix.CompileM.CompileM.run compileEnv blockEnv refState
          (Ix.CompileM.canonPreseedUnivs univs.toList
            (Array.mkEmpty univs.size)) = canonResult at hrun
      cases canonResult with
      | error err => simp at hrun
      | ok canonState =>
        rcases canonState with ⟨canonUnivs, canonState⟩
        simp only at hrun
        rw [run_bind] at hrun
        let keyed := canonUnivs.map fun u =>
          (Ix.CompileM.univSortKey u, u)
        let sortedUnivs := keyed.qsort fun (ka, _) (kb, _) =>
          Ix.CompileM.byteArrayCmp ka kb == .lt
        generalize Ix.CompileM.CompileM.run compileEnv blockEnv canonState
            (Ix.CompileM.internPreseedUnivs sortedUnivs.toList none) =
          univsResult at hrun
        cases univsResult with
        | error err => simp at hrun
        | ok univState =>
          rcases univState with ⟨_, univState⟩
          simp only at hrun
          cases hrun
          rfl

end Ix.Compile.Verify
