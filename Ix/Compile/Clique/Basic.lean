/-
  Ix.Compile.Clique.Basic: the term representation, the monad and the small
  helpers of the clique transport `Φ_σ` (design document
  `docs/compiler-passes.md` §5).

  **Term representation.** The transport works on the compiler's own terms,
  `Ix.Expr` (the hashed mirror of `Lean.Expr` that `CompileM` compiles), as
  Pass 1 (`Ix.Compile.Canon`) and the image generator (`Ix.Compile.Image`) do.
  Bound variables are de Bruijn indices; free variables (`Ix.Expr.fvar`) are
  used only where a binder telescope is reordered (`Telescope.lean`), under
  the reserved root `_clq_fvar`, which no input mentions.

  **Lean names.** Constants are referred to by `Ix.Name`, the content-hashed
  mirror of `Lean.Name` (`Ix.Name.fromLeanName`); a Lean name is carried as
  the `Ix.Name` with the same components, so the transport's output can be
  read back into Lean (`Ix.CanonM.uncanonExpr`) and compared with Lean's own
  constants component by component. The names of Lean's library constants
  the encodings use (`PSum`, `PProd`, `WellFounded.fix`, …) are spelled with
  double-backtick literals, so a rename in Lean breaks the build rather than
  the recogniser. Binder names and binder info are carried along but are
  metadata: the recognisers and the tests compare terms up to them (Lean's
  `Expr.eqv`, `Ix.Compile.Image.alphaEq`), as Ixon addresses do.

  Everything here is total: structural recursion, or recursion on an explicit
  bound (`fuel`) that fails loudly when exhausted.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Image.Expr
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata instantiateRev)

/-! ## The non-canonical causes the transport can report

The design document's §5.5/§7.2 causes, as far as the transport itself can
decide them. The test fixture `Tests.Ix.Compile.NonCanonical` has the full
enum (with the measurement-only `pending*` causes); `tag` agrees with it. -/

inductive Cause where
  /-- The grammar check failed; the fallback carries Lean's packing. -/
  | shape
  /-- GuessLex picked a different measure in another presentation (decided
  by the caller, who sees both presentations; the transport never reports
  it on its own). -/
  | guessLex
  /-- A theorem clique without a specification whose order could not be
  determined (Q6). -/
  | noSpec
  deriving BEq, Repr, Inhabited

def Cause.tag : Cause → String
  | .shape => "SHAPE" | .guessLex => "GUESSLEX" | .noSpec => "NOSPEC"

/-! ## Declarations -/

/-- A definition or theorem of a clique's encoding (the transport neither
needs nor produces other kinds). -/
structure Decl where
  name : Name
  levelParams : Array Name
  type : Expr
  value : Expr
  isThm : Bool := false
  deriving Inhabited

def Decl.ofConstantInfo? : ConstantInfo → Option Decl
  | .defnInfo v => some ⟨v.cnst.name, v.cnst.levelParams, v.cnst.type, v.value, false⟩
  | .thmInfo v => some ⟨v.cnst.name, v.cnst.levelParams, v.cnst.type, v.value, true⟩
  | .opaqueInfo v => some ⟨v.cnst.name, v.cnst.levelParams, v.cnst.type, v.value, false⟩
  | _ => none

/-! ## Names of the constants the encodings use -/

def leanName (n : Lean.Name) : Name := Ix.Name.fromLeanName n

def nPSum : Name := leanName ``PSum
def nPSumInl : Name := leanName ``PSum.inl
def nPSumInr : Name := leanName ``PSum.inr
def nPSumCasesOn : Name := leanName ``PSum.casesOn
def nPSigma : Name := leanName ``PSigma
def nPProd : Name := leanName ``PProd
def nPProdMk : Name := leanName ``PProd.mk
def nPProdFst : Name := leanName ``PProd.fst
def nPProdSnd : Name := leanName ``PProd.snd
def nAnd : Name := leanName ``And
def nAndIntro : Name := leanName ``And.intro
def nAndLeft : Name := leanName ``And.left
def nAndRight : Name := leanName ``And.right

/-! ## Universe levels, as Lean's `MetaM` builds them -/

def Level.isZero : Level → Bool
  | .zero _ => true
  | _ => false

/-- `succⁿ u ↦ n` (`Lean.Level.getOffset`). -/
def Level.offset : Level → Nat
  | .succ u _ => Level.offset u + 1
  | _ => 0

/-- `succⁿ u ↦ u` (`Lean.Level.getLevelOffset`). -/
def Level.base : Level → Level
  | .succ u _ => Level.base u
  | u => u

/-- `succⁿ zero` (`Lean.Level.isExplicit`). -/
def Level.isExplicit (u : Level) : Bool := Level.isZero (Level.base u)

/-- Lean's `mkLevelMax'` (`src/lean/Lean/Level.lean`, `mkLevelMaxCore`): the
simplifying `max` that `instantiateLevelParams` uses, hence the one behind
every level `getLevel` returns for an instantiated `Sort (max (max 1 u) v)`. -/
def mkLevelMax' (u v : Level) : Level :=
  let subsumes (u v : Level) : Bool :=
    if Level.isExplicit v && Level.offset u ≥ Level.offset v then true
    else match u with
      | .max u₁ u₂ _ => v == u₁ || v == u₂
      | _ => false
  if u == v then u
  else if Level.isZero u then v
  else if Level.isZero v then u
  else if subsumes u v then u
  else if subsumes v u then v
  else if Level.base u == Level.base v then
    if Level.offset u ≥ Level.offset v then u else v
  else Level.mkMax u v

def lvlOne : Level := Level.mkSucc Level.mkZero

/-- The level of `PSum α β`, `PProd α β` or `PSigma β` at `α : Sort u`,
`β : Sort v`: their declared sort `Sort (max (max 1 u) v)` instantiated as
`getLevel` instantiates it. -/
def pairLevel (u v : Level) : Level := mkLevelMax' (mkLevelMax' lvlOne u) v

/-- Lean's `Level.isAlwaysZero`. -/
def isAlwaysZero : Level → Bool
  | .zero _ => true
  | .max a b _ => isAlwaysZero a && isAlwaysZero b
  | .imax _ b _ => isAlwaysZero b
  | _ => false

/-! ## Term helpers -/

/-- Head constant and arguments (through `mdata` at the head). -/
def constApp? (e : Expr) : Option (Name × Array Level × Array Expr) :=
  match getAppFnArgs (stripMdata e) with
  | (.const n us _, args) => some (n, us, args)
  | _ => none

/-- `e` is an application of the constant `n` to exactly `k` arguments. -/
def isAppOfArity (e : Expr) (n : Name) (k : Nat) : Bool :=
  match constApp? e with
  | some (m, _, args) => m == n && args.size == k
  | none => false

/-- Strip `mdata` everywhere. -/
def stripAllMdata : Expr → Expr
  | .mdata _ e _ => stripAllMdata e
  | .app f a _ => Expr.mkApp (stripAllMdata f) (stripAllMdata a)
  | .lam n t b bi _ => Expr.mkLam n (stripAllMdata t) (stripAllMdata b) bi
  | .forallE n t b bi _ => Expr.mkForallE n (stripAllMdata t) (stripAllMdata b) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (stripAllMdata t) (stripAllMdata v) (stripAllMdata b) nd
  | .proj s i e _ => Expr.mkProj s i (stripAllMdata e)
  | e => e

/-- Equality up to binder names, binder info and `mdata`, with the constant
names of `b` mapped by `mapB` (the tests' comparison and the recognisers'
re-encoding check). -/
def eqUpTo (mapB : Name → Name) : Expr → Expr → Bool
  | .mdata _ a _, b => eqUpTo mapB a b
  | a, .mdata _ b _ => eqUpTo mapB a b
  | .bvar i _, .bvar j _ => i == j
  | .fvar a _, .fvar b _ => a == b
  | .mvar a _, .mvar b _ => a == b
  | .sort u _, .sort v _ => u == v
  | .const a us _, .const b vs _ => a == mapB b && us == vs
  | .app f a _, .app g b _ => eqUpTo mapB f g && eqUpTo mapB a b
  | .lam _ t b _ _, .lam _ t' b' _ _ => eqUpTo mapB t t' && eqUpTo mapB b b'
  | .forallE _ t b _ _, .forallE _ t' b' _ _ => eqUpTo mapB t t' && eqUpTo mapB b b'
  | .letE _ t v b _ _, .letE _ t' v' b' _ _ =>
    eqUpTo mapB t t' && eqUpTo mapB v v' && eqUpTo mapB b b'
  | .lit a _, .lit b _ => a == b
  | .proj s i a _, .proj s' i' b _ => s == mapB s' && i == i' && eqUpTo mapB a b
  | _, _ => false

/-- `eqUpTo` without renaming. -/
def alphaEq (a b : Expr) : Bool := eqUpTo id a b

/-- Structural equality where every variable (bound or free) matches every
variable: the recognisers' test that a packing type has the clique's
summands (whose variables are the fixed parameters, at whatever depth). -/
def eqModVars : Expr → Expr → Bool
  | .mdata _ a _, b => eqModVars a b
  | a, .mdata _ b _ => eqModVars a b
  | .bvar _ _, .bvar _ _ | .fvar _ _, .fvar _ _ | .bvar _ _, .fvar _ _
  | .fvar _ _, .bvar _ _ => true
  | .sort u _, .sort v _ => u == v
  | .const a us _, .const b vs _ => a == b && us == vs
  | .app f a _, .app g b _ => eqModVars f g && eqModVars a b
  | .lam _ t b _ _, .lam _ t' b' _ _ => eqModVars t t' && eqModVars b b'
  | .forallE _ t b _ _, .forallE _ t' b' _ _ => eqModVars t t' && eqModVars b b'
  | .letE _ t v b _ _, .letE _ t' v' b' _ _ => eqModVars t t' && eqModVars v v' && eqModVars b b'
  | .lit a _, .lit b _ => a == b
  | .proj s i a _, .proj s' i' b _ => s == s' && i == i' && eqModVars a b
  | _, _ => false

/-- Replace loose `bvar 0` of `body` by `t`, where `t` lives in the same
context as `body` (so its own `bvar 0` is the same binder): no variable is
lowered. Used to instantiate a motive `λ x. M` at `pre(z)` under a new
binder `z`. -/
def substBVar0Same (body t : Expr) : Expr := go body 0
where
  go : Expr → Nat → Expr
    | e@(.bvar i _), d => if i == d then liftLoose t d else e
    | .app f a _, d => Expr.mkApp (go f d) (go a d)
    | .lam n ty b bi _, d => Expr.mkLam n (go ty d) (go b (d + 1)) bi
    | .forallE n ty b bi _, d => Expr.mkForallE n (go ty d) (go b (d + 1)) bi
    | .letE n ty v b nd _, d => Expr.mkLetE n (go ty d) (go v d) (go b (d + 1)) nd
    | .proj s i x _, d => Expr.mkProj s i (go x d)
    | .mdata m x _, d => Expr.mkMData m (go x d)
    | e, _ => e

/-- Every loose bound variable of `e` is `≥ k` (so `e` can be lowered by
`k`). -/
def looseAllAtLeast (e : Expr) (k : Nat) : Bool := Ix.Compile.Canon.looseAtLeast e k

/-- Lower `e` by `k` when it does not mention the `k` innermost binders. -/
def lower? (e : Expr) (k : Nat) : Option Expr :=
  if looseAllAtLeast e k then some (lowerLoose e k) else none

/-- Peel `n` leading `λ`s (through `mdata`), keeping the binders. -/
def peelLams : Nat → Expr → Array (Name × Expr × Lean.BinderInfo) →
    Array (Name × Expr × Lean.BinderInfo) × Expr
  | 0, e, acc => (acc, e)
  | n + 1, e, acc =>
    match stripMdata e with
    | .lam nm t b bi _ => peelLams n b (acc.push (nm, t, bi))
    | e' => (acc, e')

def mkLams (bs : Array (Name × Expr × Lean.BinderInfo)) (body : Expr) : Expr :=
  bs.foldr (init := body) fun (nm, t, bi) acc => Expr.mkLam nm t acc bi

def lamArity : Expr → Nat
  | .lam _ _ b _ _ => lamArity b + 1
  | .mdata _ e _ => lamArity e
  | _ => 0

/-- Pre-order first occurrences of the constants satisfying `p`. -/
def constOccurrences (p : Name → Bool) (e : Expr) : Array Name := (go e (#[], {})).1
where
  go : Expr → Array Name × Std.HashSet Name → Array Name × Std.HashSet Name
    | .const n _ _, s@(acc, seen) =>
      if p n && !seen.contains n then (acc.push n, seen.insert n) else s
    | .app f a _, s => go a (go f s)
    | .lam _ t b _ _, s | .forallE _ t b _ _, s => go b (go t s)
    | .letE _ t v b _ _, s => go b (go v (go t s))
    | .proj _ _ x _, s | .mdata _ x _, s => go x s
    | _, s => s

/-- Rename constants (and projection structure names are left alone). -/
def renameConsts (m : Name → Option Name) : Expr → Expr
  | e@(.const n us _) => match m n with
    | some n' => Expr.mkConst n' us
    | none => e
  | .app f a _ => Expr.mkApp (renameConsts m f) (renameConsts m a)
  | .lam n t b bi _ => Expr.mkLam n (renameConsts m t) (renameConsts m b) bi
  | .forallE n t b bi _ => Expr.mkForallE n (renameConsts m t) (renameConsts m b) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (renameConsts m t) (renameConsts m v) (renameConsts m b) nd
  | .proj s i x _ => Expr.mkProj s i (renameConsts m x)
  | .mdata d x _ => Expr.mkMData d (renameConsts m x)
  | e => e

/-- `e` mentions the constant `n`. -/
def mentions (n : Name) : Expr → Bool
  | .const m _ _ => m == n
  | .app f a _ => mentions n f || mentions n a
  | .lam _ t b _ _ | .forallE _ t b _ _ => mentions n t || mentions n b
  | .letE _ t v b _ _ => mentions n t || mentions n v || mentions n b
  | .proj _ _ x _ | .mdata _ x _ => mentions n x
  | _ => false

/-! ## Permutations -/

/-- `σ` is a permutation of `Fin n`, given as the array `σ[i]` = canonical
position of Lean's member `i`. -/
def isPerm (σ : Array Nat) : Bool :=
  let n := σ.size
  (List.range n).all fun p => (σ.toList.filter (· == p)).length == 1

/-- The inverse permutation: `inv[p]` = Lean index at canonical position `p`. -/
def invPerm (σ : Array Nat) : Array Nat :=
  (List.range σ.size).toArray.map fun p => (σ.idxOf? p).getD p

/-- Reorder `xs` (indexed by Lean index) into canonical order. -/
def permute {α} [Inhabited α] (σ : Array Nat) (xs : Array α) : Array α :=
  (invPerm σ).map fun i => xs[i]!

/-! ## The transport monad -/

/-- The transport's state: a fresh-variable counter, and the trace (for the
tests' logs). -/
structure TState where
  next : Nat := 0
  log : Array String := #[]
  /-- `Φ` is a function of the term alone (de Bruijn, no context), so it is
  memoised by the term's hash: Lean's proof terms are heavily shared DAGs. -/
  cache : Std.HashMap Expr Expr := {}
  /-- the same for a `Φ` that depends on the binder context (structural
  recursion types paths into `below` dictionaries): keyed by the term's and
  the context's hashes, both checked on a hit. -/
  cacheCtx : Std.HashMap UInt64 (Expr × Array Expr × Expr) := {}

/-- Pure, over `Except String`: an error is a grammar failure (or an
exhausted bound), which the caller turns into the faithful fallback. -/
abbrev TM := StateT TState (Except String)

def TM.run' {α} (x : TM α) : Except String α := StateT.run' x {}

def trace (s : String) : TM Unit := modify fun st => { st with log := st.log.push s }

def liftE {α} : Except String α → TM α
  | .ok a => pure a
  | .error e => throw e

def fvarRoot : Name := Ix.Name.mkStr Ix.Name.mkAnon "_clq_fvar"

def freshFVar : TM Name :=
  modifyGet fun st => (Ix.Name.mkNat fvarRoot st.next, { st with next := st.next + 1 })

/-- A generous bound on recursion depth (term depth plus the nesting of the
encodings); exhausting it is reported as an error, never silently. -/
def defaultFuel : Nat := 1000000

end Ix.Compile.Clique

end
