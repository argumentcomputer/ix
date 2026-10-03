/-
  Ix.Compile.Clique.Packing: the right-nested binary packings of the clique
  encodings, step (A) of the transport (design document §5.0).

  Two packings, both nested to the right, as `Lean.Meta.ArgsPacker.Mutual`
  and `Lean.Meta.PProdN` build them (Lean 4.34.1):

  * **sums** `PSum D₀ (PSum D₁ … D_{n-1})` (well-founded recursion): the
    type, its injections `inj_i v = inr (… (inr (inl v)))` (`inr^{n-1} v` for
    the last summand), and its case trees (`PSum.casesOn` nested in the second
    alternative, with any motive and any number of extra arguments threaded
    through the alternatives: `Mutual.casesOn`, `mkCodomain`, and the
    refinement `processSumCasesOn` of `WF/Fix.lean`);
  * **products** `PProd R₀ (PProd R₁ … R_{n-1})`, or `And` where both sides
    are propositions (`mkPProd`): the type, its tuples (`PProd.mk` /
    `And.intro`), and its projection paths (`.proj PProd 1` … `.proj PProd 0`).

  For every construct there is a decoder (`decode*`, `none` when the term is
  not of that shape) and a builder that re-encodes from the decoded parts in
  any order. Decoders are checked by re-encoding: a term is accepted only when
  the builder, run in Lean's own order on the decoded parts, gives the term
  back (up to binder names and `mdata`). The recogniser is therefore exactly
  the image of Lean's construction, and rebuilding in the canonical order is
  Lean's construction run on the canonical order. Levels are those Lean
  computes (`pairLevel`: `getLevel` of an instantiated `Sort (max (max 1 u) v)`).
-/
module
public import Ix.Compile.Clique.Basic
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata)

inductive PackKind where
  | psum
  | pprod
  deriving BEq, Repr, Inhabited

/-- A decoded packing type: its leaves in packing order and their levels
(`0` for a leaf of an `And` node). -/
structure Spine where
  kind : PackKind
  leaves : Array Expr
  lvls : Array Level
  deriving Inhabited

def Spine.size (s : Spine) : Nat := s.leaves.size

/-- The level of a node over a leaf of level `l` and a rest of level `r`. -/
def nodeLevel (k : PackKind) (l r : Level) : Level :=
  match k with
  | .psum => pairLevel l r
  | .pprod => if isAlwaysZero l && isAlwaysZero r then Level.mkZero else pairLevel l r

/-- The node type former applied to a leaf and a rest. -/
def mkNode (k : PackKind) (l r : Level) (a b : Expr) : Expr :=
  match k with
  | .psum => mkAppN (Expr.mkConst nPSum #[l, r]) #[a, b]
  | .pprod =>
    if isAlwaysZero l && isAlwaysZero r then mkAppN (Expr.mkConst nAnd #[]) #[a, b]
    else mkAppN (Expr.mkConst nPProd #[l, r]) #[a, b]

/-- `S_k` (the suffix type from leaf `k`) and its level, for `k < n`. -/
def Spine.suffixes (s : Spine) : Array (Expr × Level) := Id.run do
  let n := s.size
  if n == 0 then return #[]
  let mut acc : Array (Expr × Level) := #[(s.leaves[n-1]!, s.lvls[n-1]!)]
  for j in (List.range (n - 1)).reverse do
    let (r, lr) := acc.back!
    acc := acc.push (mkNode s.kind s.lvls[j]! lr s.leaves[j]! r, nodeLevel s.kind s.lvls[j]! lr)
  return acc.reverse

/-- The packing type itself (`S_0`). -/
def Spine.type (s : Spine) : Expr := (s.suffixes[0]!).1

/-- The same packing with its leaves (and their levels) in another order:
`σ[i]` is the new position of leaf `i`. -/
def Spine.permute (s : Spine) (σ : Array Nat) : Spine :=
  { s with leaves := Ix.Compile.Clique.permute σ s.leaves, lvls := Ix.Compile.Clique.permute σ s.lvls }

/-- One node: `(leaf level, rest level, leaf, rest)`. -/
def decodeNode (k : PackKind) (e : Expr) : Option (Level × Level × Expr × Expr) :=
  match k, constApp? e with
  | .psum, some (n, #[l, r], #[a, b]) => if n == nPSum then some (l, r, a, b) else none
  | .pprod, some (n, #[l, r], #[a, b]) => if n == nPProd then some (l, r, a, b) else none
  | .pprod, some (n, #[], #[a, b]) =>
    if n == nAnd then some (Level.mkZero, Level.mkZero, a, b) else none
  | _, _ => none

/-- Decode an `n`-leaf packing type (`n ≥ 2`): walk `n - 1` nodes to the
right. The last right child is a leaf, whatever its shape. -/
def decodeSpine (k : PackKind) (n : Nat) (e : Expr) : Option Spine := do
  if n < 2 then none
  let mut cur := e
  let mut leaves : Array Expr := #[]
  let mut lvls : Array Level := #[]
  let mut lastR := Level.mkZero
  for _ in [0:n-1] do
    let (l, r, a, b) ← decodeNode k cur
    leaves := leaves.push a
    lvls := lvls.push l
    lastR := r
    cur := b
  leaves := leaves.push cur
  lvls := lvls.push lastR
  let s : Spine := { kind := k, leaves, lvls }
  -- the levels of the inner nodes must be the ones Lean computes
  if alphaEq s.type e then some s else none

/-! ## Sums: injections -/

/-- `inj_j v` over the packing `s` (`ArgsPacker.Mutual.pack`). -/
def mkInj (s : Spine) (j : Nat) (v : Expr) : Expr := Id.run do
  let n := s.size
  let suf := s.suffixes
  let mut acc := v
  let top := if j + 1 < n then j else n - 1
  if j + 1 < n then
    let (r, lr) := suf[j+1]!
    acc := mkAppN (Expr.mkConst nPSumInl #[s.lvls[j]!, lr]) #[s.leaves[j]!, r, acc]
  for k in (List.range top).reverse do
    let (r, lr) := suf[k+1]!
    acc := mkAppN (Expr.mkConst nPSumInr #[s.lvls[k]!, lr]) #[s.leaves[k]!, r, acc]
  return acc

/-- Decode an injection into an `n`-summand packing: its packing, the index,
the injected value. Checked by re-encoding. -/
def decodeInj (n : Nat) (e : Expr) : Option (Spine × Nat × Expr) := do
  let (h, us, args) ← constApp? e
  unless (h == nPSumInl || h == nPSumInr) && args.size == 3 && us.size == 2 do none
  let s ← decodeSpine .psum n (mkAppN (Expr.mkConst nPSum us) #[args[0]!, args[1]!])
  -- follow the chain
  let mut cur := e
  let mut idx := 0
  let mut found : Option Expr := none
  for _ in [0:n-1] do
    if found.isSome then break
    match constApp? cur with
    | some (h', _, #[_, _, v]) =>
      if h' == nPSumInl then found := some v
      else if h' == nPSumInr then
        idx := idx + 1
        cur := v
      else none
    | _ => none
  let v := found.getD cur
  if idx ≥ n then none
  if alphaEq (mkInj s idx v) e then some (s, idx, v) else none

/-! ## Sums: case trees -/

/-- A decoded case tree over an `n`-summand packing. -/
structure Tree where
  spine : Spine
  /-- the motive's result level (`PSum.casesOn`'s first level), equal at
  every node -/
  w : Level
  /-- the body of the top motive `λ x. M` -/
  motiveBody : Expr
  motiveName : Name
  major : Expr
  /-- the alternative for summand `i`, in the top context -/
  leaves : Array Expr
  /-- the arguments threaded through the alternatives -/
  extras : Array Expr
  /-- binder names of the inner alternatives (the summand variable and the
  extra arguments), for readability only -/
  altNames : Array Name
  deriving Inhabited

/-- `pre_k(t) = inr (… (inr t))` (`k` times) over the packing: the term of
type `S_0` that the inner alternatives' variable stands for. -/
def mkPrefix (s : Spine) (k : Nat) (t : Expr) : Expr := Id.run do
  let suf := s.suffixes
  let mut acc := t
  for j in (List.range k).reverse do
    let (r, lr) := suf[j+1]!
    acc := mkAppN (Expr.mkConst nPSumInr #[s.lvls[j]!, lr]) #[s.leaves[j]!, r, acc]
  return acc

/-- Peel `r` leading `∀`s (through `mdata`), returning the domains as
consecutive binders. -/
def forallDomains (r : Nat) (e : Expr) : Option (Array (Name × Expr)) := do
  let mut cur := e
  let mut acc := #[]
  for _ in [0:r] do
    match stripMdata cur with
    | .forallE nm t b _ _ => acc := acc.push (nm, t); cur := b
    | _ => none
  return acc

/-- `M[x := pre_k(z)]` for the motive body `M` (in the top context plus the
motive binder), placed under `dk` alternative binders and a new binder `z`
(`bvar 0`). -/
def motiveAt (t : Tree) (k dk : Nat) : Expr :=
  let m := liftLoose t.motiveBody dk 1
  let s' : Spine := { t.spine with leaves := t.spine.leaves.map (liftLoose · (dk + 1)) }
  substBVar0Same m (mkPrefix s' k (Expr.mkBVar 0))

/-- Build the case tree (Lean's construction) at node `k`, under `dk`
binders introduced by the alternatives above it. All parts of `t` live in the
top context and are lifted here. -/
def buildTreeAt (t : Tree) : Nat → Nat → Nat → Expr → Array Expr → Option Expr
  | 0, _, _, _, _ => none
  | fuel + 1, k, dk, major, extras => do
    let s := t.spine
    let n := s.size
    let suf := s.suffixes
    let r := t.extras.size
    let (sk, _) ← suf[k]?
    let (sk1, lk1) ← suf[k+1]?
    let motive := Expr.mkLam t.motiveName (liftLoose sk dk) (motiveAt t k dk) .default
    let alt1 := liftLoose (← t.leaves[k]?) dk
    let alt2 ← if k + 2 == n then pure (liftLoose (← t.leaves[n-1]?) dk) else do
      -- λ (z : S_{k+1}) (e₁ … e_r). tree_{k+1} z e₁ … e_r
      let ds ← forallDomains r (motiveAt t (k + 1) dk)
      let inner ← buildTreeAt t fuel (k + 1) (dk + 1 + r) (Expr.mkBVar r)
        ((List.range r).toArray.map fun i => Expr.mkBVar (r - 1 - i))
      let body := ds.zipIdx.foldr (init := inner) fun ((nm, ty), i) acc =>
        Expr.mkLam ((t.altNames[i+1]?).getD nm) ty acc .default
      let zName := (t.altNames[0]?).getD (Ix.Name.mkStr Ix.Name.mkAnon "_x")
      pure (Expr.mkLam zName (liftLoose sk1 dk) body .default)
    let head := Expr.mkConst nPSumCasesOn #[t.w, (← s.lvls[k]?), lk1]
    pure (mkAppN head (#[liftLoose (← s.leaves[k]?) dk, liftLoose sk1 dk, motive, major, alt1,
      alt2] ++ extras))

/-- The whole tree. -/
def Tree.build (t : Tree) : Option Expr :=
  if t.spine.size < 2 then none else
  buildTreeAt t (t.spine.size + 2) 0 0 t.major t.extras

/-- Decode a case tree over an `n`-summand packing, checked by re-encoding. -/
def decodeTree (n : Nat) (e : Expr) : Option Tree := do
  let (h, us, args) ← constApp? e
  unless h == nPSumCasesOn && us.size == 3 && args.size ≥ 6 do none
  let s ← decodeSpine .psum n (mkAppN (Expr.mkConst nPSum #[us[1]!, us[2]!]) #[args[0]!, args[1]!])
  let w := us[0]!
  let (mName, mBody) ← match stripMdata args[2]! with
    | .lam nm _ b _ _ => some (nm, b)
    | _ => none
  let extras := args.extract 6 args.size
  let r := extras.size
  -- walk the nested second alternatives
  let mut leaves : Array Expr := #[args[4]!]
  let mut cur := args[5]!
  let mut names : Array Name := #[]
  for k in [1:n-1] do
    -- cur = λ z e₁ … e_r. PSum.casesOn … z alt1 alt2 e₁ … e_r
    let (bs, body) := peelLams (1 + r) cur #[]
    unless bs.size == 1 + r do none
    if names.isEmpty then names := bs.map (·.1)
    let (h', _, args') ← constApp? body
    unless h' == nPSumCasesOn && args'.size == 6 + r do none
    let depth := k * (1 + r)
    leaves := leaves.push (← lower? args'[4]! depth)
    cur := args'[5]!
    let _ := h'
  leaves := leaves.push (← lower? cur ((n - 2) * (1 + r)))
  let t : Tree := { spine := s, w, motiveBody := mBody, motiveName := mName, major := args[3]!,
                    leaves, extras, altNames := names }
  let e' ← t.build
  if alphaEq e' e then some t else none

/-- The tree with its leaves, spine and parts replaced (canonical order:
`σ[i]` is the new position of Lean's summand `i`). -/
def Tree.permute (t : Tree) (σ : Array Nat) : Tree :=
  { t with spine := t.spine.permute σ, leaves := Ix.Compile.Clique.permute σ t.leaves }

/-! ## Products: tuples and projections -/

/-- `⟨c₀, ⟨c₁, … c_{n-1}⟩⟩` over the packing (`PProdN.mk`). -/
def mkTuple (s : Spine) (cs : Array Expr) : Expr := Id.run do
  let n := s.size
  let suf := s.suffixes
  let mut acc := cs[n-1]!
  for k in (List.range (n - 1)).reverse do
    let (r, lr) := suf[k+1]!
    let l := s.lvls[k]!
    acc := if isAlwaysZero l && isAlwaysZero lr then
        mkAppN (Expr.mkConst nAndIntro #[]) #[s.leaves[k]!, r, cs[k]!, acc]
      else mkAppN (Expr.mkConst nPProdMk #[l, lr]) #[s.leaves[k]!, r, cs[k]!, acc]
  return acc

/-- Decode an `n`-component tuple, checked by re-encoding. -/
def decodeTuple (n : Nat) (e : Expr) : Option (Spine × Array Expr) := do
  let (h, us, args) ← constApp? e
  unless (h == nPProdMk || h == nAndIntro) && args.size == 4 do none
  let ty := if h == nPProdMk then mkAppN (Expr.mkConst nPProd us) #[args[0]!, args[1]!]
    else mkAppN (Expr.mkConst nAnd #[]) #[args[0]!, args[1]!]
  let s ← decodeSpine .pprod n ty
  let mut cs := #[]
  let mut cur := e
  for _ in [0:n-1] do
    match constApp? cur with
    | some (_, _, #[_, _, a, b]) => cs := cs.push a; cur := b
    | _ => none
  cs := cs.push cur
  if alphaEq (mkTuple s cs) e then some (s, cs) else none

/-- The structure name of node `k` of a product packing. -/
def Spine.nodeStruct (s : Spine) (k : Nat) : Name :=
  let suf := s.suffixes
  if isAlwaysZero s.lvls[k]! && isAlwaysZero (suf[k+1]!).2 then nAnd else nPProd

/-- The projection steps `(structure, field)` from a value of the packing to
its component `j` (`PProdN.proj`): `j` times `.2`, then `.1` unless last. -/
def Spine.projSteps (s : Spine) (j : Nat) : Array (Name × Nat) := Id.run do
  let n := s.size
  let mut acc := #[]
  for k in [0:j] do acc := acc.push (s.nodeStruct k, 1)
  if j + 1 < n then acc := acc.push (s.nodeStruct j, 0)
  return acc

def applyProjs (steps : Array (Name × Nat)) (e : Expr) : Expr :=
  steps.foldl (init := e) fun acc (s, i) => Expr.mkProj s i acc

/-- Which component a step sequence selects, for `n` components (`none`
when it is not a full path to a component). -/
def pathIndex (n : Nat) (steps : Array (Name × Nat)) : Option Nat :=
  if n < 2 then (if steps.isEmpty then some 0 else none) else
  let ones := steps.takeWhile (·.2 == 1)
  let k := ones.size
  if k + 1 < n then
    if steps.size == k + 1 && (steps[k]!).2 == 0 then some k else none
  else if k == n - 1 && steps.size == k then some (n - 1)
  else none

end Ix.Compile.Clique

end
