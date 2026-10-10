/-
  Ix.Compile.Canon.Expr: total expression and level helpers for Pass 1.

  Pass 1 (`Ix.Compile.Canon.*`) is written as total pure functions over the
  compiler's own data types (`Ix.Name`, `Ix.Level`, `Ix.Expr`,
  `Ix.ConstantInfo`). The compiler's helpers it needs (`Ix.AuxGen.ExprUtils`,
  `Ix.AuxGen.Nested`) are `partial` or loop-based, so the ones Pass 1 uses are
  restated here by structural recursion, with the same results:

  * names: `namePretty` (Rust `Name::pretty`, `Ix.Name.pretty`),
    `nameReplacePrefix` (`Ix.AuxGen.nameReplacePrefix`);
  * applications: `getAppFnArgs` (`decomposeApps`), `mkAppN`;
  * de Bruijn arithmetic: `liftLoose` (`shiftVars`), `lowerLoose`
    (`lowerVars`), `instantiateRevAt`/`instantiateRev`,
    `instantiatePiParams`, `looseAtLeast`;
  * universes: `levelPeelSucc`, `levelMaxSmart`, `levelImaxSmart`,
    `substLevel`/`substLevels` (the smart constructors the compiler applies
    when it instantiates an external inductive at a nested occurrence),
    `normalizeLevel`/`levelAlphaEq` (Rust `congruence::level_alpha_eq`);
  * name rewriting: `replaceConstNames` (also renames projection structure
    names) and `canonicalizeConstNames` (does not), as in the compiler;
  * binder telescopes: `peelForalls` (`forallTelescope`'s shape: `mdata`
    stripped before each binder) and `mkForalls`.

  None of these is cached: they run on constructor types and nested
  occurrences, which are small. The reference walk (`Graph.lean`) and the
  comparator (`Order.lean`) are the only Pass 1 functions that see whole
  definition values; the first deduplicates by hash, the second recurses on
  the pair of terms.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.OccurrenceKey
public import Ix.Common
public import Ix.Compile.Canon.NameTable
public section

namespace Ix.Compile.Canon

open Ix (Name Level Expr)

/-! ## Names -/

/-- Dot-separated rendering, byte for byte `Ix.Name.pretty` and Rust
`Name::pretty` (numeric components as plain digits, no escaping). The
compiler spells nested auxiliary names with it. -/
def namePretty : Name → String
  | .anonymous _ => ""
  | .str (.anonymous _) s _ => s
  | .str p s _ => s!"{namePretty p}.{s}"
  | .num (.anonymous _) n _ => s!"{n}"
  | .num p n _ => s!"{namePretty p}.{n}"

/-- The components of `name` below `pre`, root first, or `none` when `name`
does not extend `pre`. -/
def stripPrefix (name pre : Name) : Option (List (String ⊕ Nat)) :=
  if keyName name = keyName pre then some []
  else match name with
    | .str p s _ => (stripPrefix p pre).map (· ++ [.inl s])
    | .num p i _ => (stripPrefix p pre).map (· ++ [.inr i])
    | .anonymous _ => none

/-- Replace the prefix `old` of `name` by `new` (`A.B.mk`, `A.B` ↦ `X.Y`
gives `X.Y.mk`); a name not extending `old` is returned unchanged.
`Ix.AuxGen.nameReplacePrefix`. -/
def nameReplacePrefix (name old new : Name) : Name :=
  match stripPrefix name old with
  | some suffix => suffix.foldl (init := new) fun acc c =>
      match c with
      | .inl s => Name.mkStr acc s
      | .inr i => Name.mkNat acc i
  | none => name

/-! ## Applications -/

/-- `f a₁ … aₙ ↦ (f, #[a₁, …, aₙ])`. -/
def getAppFnArgs : Expr → Expr × Array Expr
  | .app f a _ =>
    let (h, args) := getAppFnArgs f
    (h, args.push a)
  | e => (e, #[])

def mkAppN (f : Expr) (args : Array Expr) : Expr :=
  args.foldl Expr.mkApp f

/-! ## de Bruijn arithmetic -/

/-- Add `n` to every loose bound variable `≥ cutoff`. -/
def liftLoose (e : Expr) (n : Nat) (cutoff : Nat := 0) : Expr :=
  if n == 0 then e else go e cutoff
where
  go : Expr → Nat → Expr
    | .bvar i _, c => if i ≥ c then Expr.mkBVar (i + n) else Expr.mkBVar i
    | .app f a _, c => Expr.mkApp (go f c) (go a c)
    | .lam nm t b bi _, c => Expr.mkLam nm (go t c) (go b (c + 1)) bi
    | .forallE nm t b bi _, c => Expr.mkForallE nm (go t c) (go b (c + 1)) bi
    | .letE nm t v b nd _, c => Expr.mkLetE nm (go t c) (go v c) (go b (c + 1)) nd
    | .proj nm i s _, c => Expr.mkProj nm i (go s c)
    | .mdata md x _, c => Expr.mkMData md (go x c)
    | e, _ => e

/-- Subtract `n` from every loose bound variable `≥ cutoff + n`; variables in
`[cutoff, cutoff + n)` are left as they are (callers check there are none). -/
def lowerLoose (e : Expr) (n : Nat) (cutoff : Nat := 0) : Expr :=
  if n == 0 then e else go e cutoff
where
  go : Expr → Nat → Expr
    | .bvar i _, c => if i ≥ c + n then Expr.mkBVar (i - n) else Expr.mkBVar i
    | .app f a _, c => Expr.mkApp (go f c) (go a c)
    | .lam nm t b bi _, c => Expr.mkLam nm (go t c) (go b (c + 1)) bi
    | .forallE nm t b bi _, c => Expr.mkForallE nm (go t c) (go b (c + 1)) bi
    | .letE nm t v b nd _, c => Expr.mkLetE nm (go t c) (go v c) (go b (c + 1)) nd
    | .proj nm i s _, c => Expr.mkProj nm i (go s c)
    | .mdata md x _, c => Expr.mkMData md (go x c)
    | e, _ => e

/-- Every loose bound variable of `e` (relative to `e`) is `≥ d`: under `d`
binders entered below a telescope, `e` refers only to the telescope. -/
def looseAtLeast (e : Expr) (d : Nat) : Bool := go e 0
where
  go : Expr → Nat → Bool
    | .bvar i _, k => i < k || i - k ≥ d
    | .app f a _, k => go f k && go a k
    | .lam _ t b _ _, k | .forallE _ t b _ _, k => go t k && go b (k + 1)
    | .letE _ t v b _ _, k => go t k && go v k && go b (k + 1)
    | .proj _ _ s _, k | .mdata _ s _, k => go s k
    | _, _ => true

/-- Replace loose `bvar (depth + i)` (`i < args.size`) by `args[i]` lifted by
`depth`, and lower the loose variables past them by `args.size`
(`Ix.AuxGen.instantiateRevAt`). -/
def instantiateRevAt (args : Array Expr) : Expr → Nat → Expr
  | .bvar i _, depth =>
    if i ≥ depth then
      let r := i - depth
      if h : r < args.size then liftLoose args[r] depth
      else Expr.mkBVar (i - args.size)
    else Expr.mkBVar i
  | .app f a _, d => Expr.mkApp (instantiateRevAt args f d) (instantiateRevAt args a d)
  | .lam nm t b bi _, d =>
    Expr.mkLam nm (instantiateRevAt args t d) (instantiateRevAt args b (d + 1)) bi
  | .forallE nm t b bi _, d =>
    Expr.mkForallE nm (instantiateRevAt args t d) (instantiateRevAt args b (d + 1)) bi
  | .letE nm t v b nd _, d =>
    Expr.mkLetE nm (instantiateRevAt args t d) (instantiateRevAt args v d)
      (instantiateRevAt args b (d + 1)) nd
  | .proj nm i s _, d => Expr.mkProj nm i (instantiateRevAt args s d)
  | .mdata md x _, d => Expr.mkMData md (instantiateRevAt args x d)
  | e, _ => e

def instantiateRev (body : Expr) (args : Array Expr) : Expr :=
  if args.isEmpty then body else instantiateRevAt args body 0

/-- Peel `n` leading `∀`s of `typ`, substituting `args[i]` for the `i`-th
(`Ix.AuxGen.instantiatePiParams`; stops at the first non-`∀`, without
looking through `mdata`). The arguments may have loose variables: they are
lifted under the binders that remain. -/
def instantiatePiParams (typ : Expr) (n : Nat) (args : Array Expr) : Expr :=
  go typ (args.toList.take n)
where
  go : Expr → List Expr → Expr
    | .forallE _ _ body _ _, a :: as => go (instantiateRev body #[a]) as
    | e, _ => e

/-- Strip `mdata` wrappers at the head. -/
def stripMdata : Expr → Expr
  | .mdata _ x _ => stripMdata x
  | e => e

/-- One binder of a telescope: name, domain, binder info. -/
abbrev Binder := Name × Expr × Lean.BinderInfo

/-- Peel up to `n` leading `∀` binders, stripping `mdata` before each (the
shape of `Ix.AuxGen.forallTelescope`), without instantiating: the body keeps
the peeled binders as loose variables, `bvar 0` the last. -/
def peelForalls : Nat → Expr → Array Binder → Array Binder × Expr
  | 0, e, acc => (acc, e)
  | n + 1, e, acc =>
    match stripMdata e with
    | .forallE nm t b bi _ => peelForalls n b (acc.push (nm, t, bi))
    | e' => (acc, e')

/-- `∀ binders, body`, binders outermost first. -/
def mkForalls (binders : Array Binder) (body : Expr) : Expr :=
  binders.foldr (init := body) fun (nm, t, bi) acc => Expr.mkForallE nm t acc bi

/-! ## Universes -/

/-- Scalar universe equality ignores every cached name and level field. -/
def levelSameStructure (a b : Level) : Bool :=
  decide (keyLevelShape a = keyLevelShape b)

/-- `succⁿ base ↦ (base, n)`. -/
def levelPeelSucc : Level → Level × Nat
  | .succ l _ => let (b, n) := levelPeelSucc l; (b, n + 1)
  | l => (l, 0)

def levelExplicitOffset (l : Level) : Option Nat :=
  match levelPeelSucc l with
  | (.zero _, n) => some n
  | _ => none

/-- `Ix.AuxGen.levelMaxSmart` (Rust `Level::max_smart`). -/
def levelMaxSmart (x y : Level) : Level :=
  match levelExplicitOffset x, levelExplicitOffset y with
  | some ox, some oy => if ox ≥ oy then x else y
  | _, _ =>
    if levelSameStructure x y then x
    else match x, y with
      | .zero _, _ => y
      | _, .zero _ => x
      | _, _ =>
        let yAbsorbs := match y with
          | .max bl br _ => levelSameStructure bl x || levelSameStructure br x
          | _ => false
        if yAbsorbs then y
        else
          let xAbsorbs := match x with
            | .max al ar _ => levelSameStructure al y || levelSameStructure ar y
            | _ => false
          if xAbsorbs then x
          else
            let (bx, ox) := levelPeelSucc x
            let (by_, oy) := levelPeelSucc y
            if levelSameStructure bx by_ then (if ox ≥ oy then x else y)
            else Level.mkMax x y

/-- `Ix.AuxGen.levelImaxSmart` (Rust `Level::imax_smart`). -/
def levelImaxSmart (x y : Level) : Level :=
  match y with
  | .succ .. => levelMaxSmart x y
  | .zero _ => y
  | _ =>
    match x with
    | .zero _ => y
    | .succ (.zero _) _ => y
    | _ => if levelSameStructure x y then x else Level.mkIMax x y

/-- `Ix.AuxGen.substLevel`: parameters by name, through the smart
constructors. -/
def substLevel (params : Array Name) (univs : Array Level) : Level → Level
  | .succ l _ => Level.mkSucc (substLevel params univs l)
  | .max a b _ => levelMaxSmart (substLevel params univs a) (substLevel params univs b)
  | .imax a b _ => levelImaxSmart (substLevel params univs a) (substLevel params univs b)
  | l@(.param nm _) =>
    match (params.map keyName).idxOf? (keyName nm) with
    | some i => univs[i]?.getD l
    | none => l
  | l => l

/-- `Ix.AuxGen.substLevels`. -/
def substLevels (params : Array Name) (univs : Array Level) (e : Expr) : Expr :=
  if params.isEmpty || univs.isEmpty then e else go e
where
  go : Expr → Expr
    | .sort l _ => Expr.mkSort (substLevel params univs l)
    | .const nm us _ => Expr.mkConst nm (us.map (substLevel params univs))
    | .app f a _ => Expr.mkApp (go f) (go a)
    | .lam nm t b bi _ => Expr.mkLam nm (go t) (go b) bi
    | .forallE nm t b bi _ => Expr.mkForallE nm (go t) (go b) bi
    | .letE nm t v b nd _ => Expr.mkLetE nm (go t) (go v) (go b) nd
    | .proj nm i s _ => Expr.mkProj nm i (go s)
    | .mdata md x _ => Expr.mkMData md (go x)
    | e => e

/-- `Ix.AuxGen.normalizeLevel`: bottom-up through the smart constructors. -/
def normalizeLevel : Level → Level
  | .succ l _ => Level.mkSucc (normalizeLevel l)
  | .max a b _ => levelMaxSmart (normalizeLevel a) (normalizeLevel b)
  | .imax a b _ => levelImaxSmart (normalizeLevel a) (normalizeLevel b)
  | l => l

/-- `Ix.AuxGen.levelAlphaEqStruct`: structural, any two parameters equal. -/
def levelAlphaEqStruct : Level → Level → Bool
  | .zero _, .zero _ => true
  | .succ a _, .succ b _ => levelAlphaEqStruct a b
  | .max a1 a2 _, .max b1 b2 _ => levelAlphaEqStruct a1 b1 && levelAlphaEqStruct a2 b2
  | .imax a1 a2 _, .imax b1 b2 _ => levelAlphaEqStruct a1 b1 && levelAlphaEqStruct a2 b2
  | .param .., .param .. => true
  | _, _ => false

def levelAlphaEq (a b : Level) : Bool :=
  levelAlphaEqStruct (normalizeLevel a) (normalizeLevel b)

/-! ## Name rewriting -/

/-- Rename constants and projection structure names
(`Ix.AuxGen.replaceConstNamesCached`). -/
def replaceConstNames (map : Std.HashMap Name Name) (e : Expr) : Expr :=
  if map.isEmpty then e else go e
where
  go : Expr → Expr
    | .const nm ls _ => Expr.mkConst ((map.get? nm).getD nm) ls
    | .app f a _ => Expr.mkApp (go f) (go a)
    | .lam nm t b bi _ => Expr.mkLam nm (go t) (go b) bi
    | .forallE nm t b bi _ => Expr.mkForallE nm (go t) (go b) bi
    | .letE nm t v b nd _ => Expr.mkLetE nm (go t) (go v) (go b) nd
    | .proj nm i s _ => Expr.mkProj ((map.get? nm).getD nm) i (go s)
    | .mdata md x _ => Expr.mkMData md (go x)
    | e => e

/-- Rename constants only, keeping projection structure names
(`Ix.AuxGen.canonicalizeConstNames`). -/
def canonicalizeConstNames (map : Std.HashMap Name Name) (e : Expr) : Expr :=
  if map.isEmpty then e else go e
where
  go : Expr → Expr
    | e@(.const nm ls _) =>
      match map.get? nm with
      | some nm' => Expr.mkConst nm' ls
      | none => e
    | .app f a _ => Expr.mkApp (go f) (go a)
    | .lam nm t b bi _ => Expr.mkLam nm (go t) (go b) bi
    | .forallE nm t b bi _ => Expr.mkForallE nm (go t) (go b) bi
    | .letE nm t v b nd _ => Expr.mkLetE nm (go t) (go v) (go b) nd
    | .proj nm i s _ => Expr.mkProj nm i (go s)
    | .mdata md x _ => Expr.mkMData md (go x)
    | e => e

/-- Some constant or projection structure name of `e` is in `names`
(`Ix.AuxGen.exprMentionsAnyName`). -/
def mentionsAnyName (names : Std.HashSet Name) (e : Expr) : Bool :=
  !names.isEmpty && go e
where
  go : Expr → Bool
    | .const nm _ _ => names.contains nm
    | .app f a _ => go f || go a
    | .lam _ t b _ _ | .forallE _ t b _ _ => go t || go b
    | .letE _ t v b _ _ => go t || go v || go b
    | .proj nm _ s _ => names.contains nm || go s
    | .mdata _ s _ => go s
    | _ => false

/-- Constants of `e` (constant heads only, not projection structure names)
that are in `names`. -/
def constsIn (names : Std.HashSet Name) (e : Expr) : Std.HashSet Name := go e {}
where
  go : Expr → Std.HashSet Name → Std.HashSet Name
    | .const nm _ _, acc => if names.contains nm then acc.insert nm else acc
    | .app f a _, acc => go a (go f acc)
    | .lam _ t b _ _, acc | .forallE _ t b _ _, acc => go b (go t acc)
    | .letE _ t v b _ _, acc => go b (go v (go t acc))
    | .proj nm _ s _, acc => go s (if names.contains nm then acc.insert nm else acc)
    | .mdata _ s _, acc => go s acc
    | _, acc => acc

end Ix.Compile.Canon

end
