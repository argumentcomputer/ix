import Ix.CompileM

/-!
# Expression metadata arena refinement

The production compiler returns a canonical `Ixon.Expr` together with a
`UInt64` root into an append-only presentation arena.  This module gives the
root a structural meaning independent of decompilation and isolates the
finite-capacity premise needed to justify `Nat.toUInt64` allocation indices.
-/

namespace Ix.Compile.Verify

/-- Number of metadata nodes allocated by a cache-free ordinary compilation.
Cache hits can only reduce this cost. -/
def exprArenaCost : Ix.Expr → Nat
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 1
  | .app fn arg .. => exprArenaCost fn + exprArenaCost arg + 1
  | .lam _ ty body .. | .forallE _ ty body .. =>
    exprArenaCost ty + exprArenaCost body + 1
  | .letE _ ty val body .. =>
    exprArenaCost ty + exprArenaCost val + exprArenaCost body + 1
  | .proj _ _ value .. => exprArenaCost value + 1
  | .mdata _ inner .. => exprArenaCost inner + 1

theorem exprArenaCost_pos (source : Ix.Expr) : 0 < exprArenaCost source := by
  induction source <;> simp [exprArenaCost, *]

/-- Every node already readable in `before` remains readable at the same
wire index in `after`. -/
def ArenaExtends (before after : Ixon.ExprMetaArena) : Prop :=
  ∀ {idx : UInt64} {node : Ixon.ExprMetaData},
    before.nodes[idx.toNat]? = some node →
    after.nodes[idx.toNat]? = some node

theorem ArenaExtends.refl (arena : Ixon.ExprMetaArena) :
    ArenaExtends arena arena := by
  intro idx node hnode
  exact hnode

theorem ArenaExtends.trans {first second third : Ixon.ExprMetaArena}
    (hfirst : ArenaExtends first second)
    (hsecond : ArenaExtends second third) :
    ArenaExtends first third := by
  intro idx node hnode
  exact hsecond (hfirst hnode)

theorem ArenaExtends.push (arena : Ixon.ExprMetaArena)
    (node : Ixon.ExprMetaData) :
    ArenaExtends arena { nodes := arena.nodes.push node } := by
  intro idx found hfound
  have hlt : idx.toNat < arena.nodes.size :=
    (Array.getElem?_eq_some_iff.mp hfound).1
  simpa [Array.getElem?_push, Nat.ne_of_lt hlt] using hfound

/-- The metadata tree rooted at a wire index has exactly the presentation
shape of its source expression.  Canonical-only fields (universe indices,
reference indices, and `letE.nonDep`) deliberately do not occur in the
sidecar relation. -/
inductive ArenaRel : Ix.Expr → UInt64 → Ixon.ExprMetaArena → Prop where
  | bvar {arena idx hash root}
      (node : arena.nodes[root.toNat]? = some .leaf) :
      ArenaRel (.bvar idx hash) root arena
  | sort {arena level hash root}
      (node : arena.nodes[root.toNat]? = some .leaf) :
      ArenaRel (.sort level hash) root arena
  | const {arena name levels hash root}
      (node : arena.nodes[root.toNat]? = some (.ref name.getHash)) :
      ArenaRel (.const name levels hash) root arena
  | app {arena fn arg hash fnRoot argRoot root}
      (fnRel : ArenaRel fn fnRoot arena)
      (argRel : ArenaRel arg argRoot arena)
      (node : arena.nodes[root.toNat]? = some (.app fnRoot argRoot)) :
      ArenaRel (.app fn arg hash) root arena
  | lam {arena name ty body bi hash tyRoot bodyRoot root}
      (tyRel : ArenaRel ty tyRoot arena)
      (bodyRel : ArenaRel body bodyRoot arena)
      (node : arena.nodes[root.toNat]? =
        some (.binder name.getHash bi tyRoot bodyRoot)) :
      ArenaRel (.lam name ty body bi hash) root arena
  | all {arena name ty body bi hash tyRoot bodyRoot root}
      (tyRel : ArenaRel ty tyRoot arena)
      (bodyRel : ArenaRel body bodyRoot arena)
      (node : arena.nodes[root.toNat]? =
        some (.binder name.getHash bi tyRoot bodyRoot)) :
      ArenaRel (.forallE name ty body bi hash) root arena
  | letE {arena name ty val body nonDep hash tyRoot valRoot bodyRoot root}
      (tyRel : ArenaRel ty tyRoot arena)
      (valRel : ArenaRel val valRoot arena)
      (bodyRel : ArenaRel body bodyRoot arena)
      (node : arena.nodes[root.toNat]? =
        some (.letBinder name.getHash tyRoot valRoot bodyRoot)) :
      ArenaRel (.letE name ty val body nonDep hash) root arena
  | lit {arena literal hash root}
      (node : arena.nodes[root.toNat]? = some .leaf) :
      ArenaRel (.lit literal hash) root arena
  | proj {arena typeName field value hash valueRoot root}
      (valueRel : ArenaRel value valueRoot arena)
      (node : arena.nodes[root.toNat]? =
        some (.prj typeName.getHash valueRoot)) :
      ArenaRel (.proj typeName field value hash) root arena
  | mdata {arena inner hash innerRoot root}
      (innerRel : ArenaRel inner innerRoot arena)
      (node : arena.nodes[root.toNat]? = some (.mdata #[#[]] innerRoot)) :
      ArenaRel (.mdata #[] inner hash) root arena

theorem ArenaRel.mono {source : Ix.Expr} {root : UInt64}
    {before after : Ixon.ExprMetaArena}
    (hrel : ArenaRel source root before)
    (hextends : ArenaExtends before after) : ArenaRel source root after := by
  induction hrel with
  | bvar node => exact .bvar (hextends node)
  | sort node => exact .sort (hextends node)
  | const node => exact .const (hextends node)
  | app fnRel argRel node ihFn ihArg =>
    exact .app (ihFn hextends) (ihArg hextends) (hextends node)
  | lam tyRel bodyRel node ihTy ihBody =>
    exact .lam (ihTy hextends) (ihBody hextends) (hextends node)
  | all tyRel bodyRel node ihTy ihBody =>
    exact .all (ihTy hextends) (ihBody hextends) (hextends node)
  | letE tyRel valRel bodyRel node ihTy ihVal ihBody =>
    exact .letE (ihTy hextends) (ihVal hextends) (ihBody hextends)
      (hextends node)
  | lit node => exact .lit (hextends node)
  | proj valueRel node ihValue =>
    exact .proj (ihValue hextends) (hextends node)
  | mdata innerRel node ihInner =>
    exact .mdata (ihInner hextends) (hextends node)

/-- Arena facts returned by one expression-compilation run. -/
structure ArenaCompileRel (source : Ix.Expr) (root : UInt64)
    (before after : Ixon.ExprMetaArena) : Prop where
  rootRel : ArenaRel source root after
  arenaExtends : ArenaExtends before after
  growth : after.nodes.size ≤ before.nodes.size + exprArenaCost source

/-- Every warm expression-cache root still denotes the metadata tree of its
cache key in the live append-only arena. -/
structure ArenaCacheWF (state : Ix.CompileM.BlockState) : Prop where
  sound : ∀ {source target root},
    state.exprCache.get? source = some (target, root) →
      ArenaRel source root state.arena

theorem ArenaCacheWF.empty :
    ArenaCacheWF (default : Ix.CompileM.BlockState) := by
  constructor
  intro source target root hlookup
  change ({} : Std.HashMap Ix.Expr (Ixon.Expr × UInt64)).get? source =
    some (target, root) at hlookup
  simp at hlookup

theorem ArenaCacheWF.of_frame {before after : Ix.CompileM.BlockState}
    (hbefore : ArenaCacheWF before)
    (hcache : after.exprCache = before.exprCache)
    (harena : ArenaExtends before.arena after.arena) :
    ArenaCacheWF after := by
  constructor
  intro source target root hlookup
  exact (hbefore.sound (hcache ▸ hlookup)).mono harena

end Ix.Compile.Verify
