/-
  Ix.Compile.Clique.PartialFixpoint: transport of a `partial_fixpoint`
  clique (design document §5.2), the steps (R), (A), (S) and (G).

  Lean's encoding (`Elab/PreDefinition/PartialFixpoint/Main.lean`,
  `Elab/Tactic/Monotonicity.lean`, Lean 4.34.1), as the transport sees it:

  * `f₀.mutual : ∀ fixed, γ` with `γ = T₀ ×' (T₁ ×' …)` (`PProdN.pack`), its
    value `λ fixed. Order.fix γ I (λ x. ⟨F₀[x], …⟩) hmono`, where `I` is the
    instance tree `instCCPOPProd T₀ (…) i₀ (…)` (`mkPackedPPRodInstance`;
    `instCompleteLatticePProd` for the lattice-theoretic fixpoints) and the
    recursive calls in `F_i` are projection paths `x.2.1` of the packed
    variable (`PProdN.proj`);
  * the monotonicity proof `hmono` (abstracted as `f₀.mutual._proof_1`):
    statement `monotone (α := γ) (toPartialOrder γ I) γ O (λ x. ⟨…⟩)`, `O` the
    tree `instPartialOrderPProd T₀ (…) (toPartialOrder T₀ i₀) (…)`; value the
    `PProd.monotone_mk` tree over the per-function proofs (`mkMonoPProd`,
    `PProdN.genMk`), whose `g` arguments are the remaining tuples;
  * in each per-function proof, the sub-proof of a recursive call through
    the path to component `j` is built by `solveMonoCall` inside out:
    `monotone_id`, then one `PProd.monotone_fst`/`monotone_snd` per step (at
    that step's `PProd` node, with the instances `toPartialOrder` of the
    node's leaf and rest), then `monotone_apply` per argument; the path
    itself also occurs in application form (`PProd.fst (PProd.snd x)`);
  * the members `f_i := λ ps. (f₀.mutual fixed).2.1 varying`.

  `Φ_σ` re-associates every packing-shaped construct (the packed type, the
  instance trees, the tuples, the paths in both forms, the `monotone_mk`
  tree) with Lean's own construction in canonical order, and **regenerates**
  (G) every `monotone_fst`/`monotone_snd` chain for the canonical path:
  the chain's length changes with the path (`.2.1` against `.1`), so it is
  rebuilt by `solveMonoCall`'s recipe, deterministically and at the term level
  (the node's leaf, rest and instances are read off the packing; no search).
  Everything else in the proofs (`monotone_const`, `monotone_ite`,
  `monotone_bind`, `monotone_apply`, `monotone_of_monotone_apply`) mentions the
  packing only through the constructs above.

  A per-function proof outside the grammar (a user-supplied monotonicity
  term, or anything the recognisers do not cover) takes the composition
  fallback of §5.2: `monotone_compose (mono φ) h`, with `φ : γ' → γ` the
  re-association `y ↦ ⟨y.π_{σ 0}, …⟩` and `mono φ` a `monotone_mk` tree over
  regenerated path proofs; it is recorded as `SHAPE`. A per-function proof is
  outside the grammar when it binds a variable whose type mentions the
  packing other than as the packed type (a user's `intro f g h` unfolds the
  order: `h : f ⊑ g` is an `And` over the packing, and `h.2` selects a factor
  by position), or when it contains a `monotone_fst`/`monotone_snd`/
  `monotone_id` over the packing that is not `solveMonoCall`'s chain (a
  user's lemma chain, with the instances its own unification found).

  The lattice-theoretic fixpoints (`inductive_fixpoint`,
  `coinductive_fixpoint`) spell a component `∀ x, ImplicationOrder` (or
  `ReverseImplicationOrder`) where the packed constant's type says
  `∀ x, Prop`; the packing is recognised up to that alias.

  **O16** (the members' faithfulness, design document §5.2, decision Q9) is
  proved in `FixPerm.lean`: `fix_iso` (`Lean.Order.fix` commutes with an
  order isomorphism), `lfp_monotone_iso` (the lattice variant), and the
  `PProd` re-associations as order isomorphisms. With `φ` the
  re-association onto the canonical packing, the canonical functional is
  `φ ∘ F ∘ φ⁻¹` up to β and projection of a constructor, so component `σ i`
  of the canonical fixpoint is component `i` of Lean's (`fix_iso_proj`).
-/
module
public import Ix.Compile.Clique.Packing
public import Ix.Compile.Clique.Telescope
public import Ix.Compile.Clique.WF
public import Ix.Compile.Clique.Structural
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata peelForalls)

def nOrderFix : Name := leanName ``Lean.Order.fix
def nInstCCPOPProd : Name := leanName ``Lean.Order.instCCPOPProd
def nInstLatticePProd : Name := leanName ``Lean.Order.instCompleteLatticePProd
def nInstPOPProd : Name := leanName ``Lean.Order.instPartialOrderPProd
def nCCPOToPO : Name := leanName ``Lean.Order.CCPO.toPartialOrder
def nLatticeToPO : Name := leanName ``Lean.Order.CompleteLattice.toPartialOrder
def nMonoMk : Name := leanName ``Lean.Order.PProd.monotone_mk
def nMonoFst : Name := leanName ``Lean.Order.PProd.monotone_fst
def nMonoSnd : Name := leanName ``Lean.Order.PProd.monotone_snd
def nMonoId : Name := leanName ``Lean.Order.monotone_id
def nMonoCompose : Name := leanName ``Lean.Order.monotone_compose

/-! ## Packing-shaped instance trees -/

/-- `h.{l_k, lev_{k+1}} D_k S_{k+1} i_k (tree k+1)`, the leaf instance last. -/
def mkInstTree (h : Name) (s : Spine) (insts : Array Expr) : Expr := Id.run do
  let n := s.size
  let suf := s.suffixes
  let mut acc := insts[n-1]!
  for k in (List.range (n - 1)).reverse do
    let (r, lr) := suf[k+1]!
    acc := mkAppN (Expr.mkConst h #[s.lvls[k]!, lr]) #[s.leaves[k]!, r, insts[k]!, acc]
  return acc

/-- Decode an instance tree over an `n`-leaf product, checked by re-encoding. -/
def decodeInstTree (n : Nat) (e : Expr) : Option (Name × Spine × Array Expr) := do
  let (h, us, args) ← constApp? e
  unless (h == nInstCCPOPProd || h == nInstLatticePProd || h == nInstPOPProd) &&
    us.size == 2 && args.size == 4 do none
  let s ← decodeSpine .pprod n (mkAppN (Expr.mkConst nPProd us) #[args[0]!, args[1]!])
  let mut insts := #[]
  let mut cur := e
  for _ in [0:n-1] do
    match constApp? cur with
    | some (h', _, #[_, _, i, rest]) => if h' == h then insts := insts.push i; cur := rest else none
    | _ => none
  insts := insts.push cur
  if alphaEq (mkInstTree h s insts) e then some (h, s, insts) else none

/-! ## Paths in application form -/

/-- `PProd.snd (… (PProd.fst x))` to component `j` (the `.1`/`.2` of a
theorem statement, after instantiation). -/
def mkPathApp (s : Spine) (j : Nat) (x : Expr) : Expr := Id.run do
  let n := s.size
  let suf := s.suffixes
  let mut acc := x
  for k in [0:j] do
    let (r, lr) := suf[k+1]!
    acc := mkAppN (Expr.mkConst nPProdSnd #[s.lvls[k]!, lr]) #[s.leaves[k]!, r, acc]
  if j + 1 < n then
    let (r, lr) := suf[j+1]!
    acc := mkAppN (Expr.mkConst nPProdFst #[s.lvls[j]!, lr]) #[s.leaves[j]!, r, acc]
  return acc

/-- Decode an application-form path: the base, the component, the spine
(from the outermost node's type arguments... read from the innermost step). -/
def decodePathApp (n : Nat) (e : Expr) : Option (Spine × Nat × Expr) := do
  -- collect the steps from the outside in
  let mut cur := e
  let mut steps : Array (Name × Array Level × Expr × Expr) := #[]
  for _ in [0:n] do
    match constApp? cur with
    | some (h, us, #[a, b, x]) =>
      if h == nPProdFst || h == nPProdSnd then
        steps := steps.push (h, us, a, b); cur := x
      else break
    | _ => break
  if steps.isEmpty then none
  -- the innermost step is at the packing's root
  let (_, us, a, b) := steps.back!
  let s ← decodeSpine .pprod n (mkAppN (Expr.mkConst nPProd us) #[a, b])
  let ones := (steps.reverse.takeWhile (·.1 == nPProdSnd)).size
  let j := if ones + 1 < n then ones else n - 1
  if alphaEq (mkPathApp s j cur) e then some (s, j, cur) else none

/-! ## The layout -/

structure PFLayout where
  n : Nat
  sigma : Array Nat
  packedName : Name
  newPackedName : Name
  numFixed : Nat
  fixedPerm : Array Nat
  /-- Lean's component types `T_i` (fixed parameters loose) -/
  leaves : Array Expr
  /-- Lean's packed type (for the projections' structure names) -/
  spine : Spine
  proofPerm : Std.HashMap Name (Array Nat) := {}
  /-- `monotone_compose`'s universe parameters (for the fallback) -/
  composeLevels : Array Name := #[]
  /-- per member (Lean's order): the member's parameter (outermost `0`) at
  each fixed position of its projection of the fixpoint -/
  memberFixed : Array (Array Nat) := #[]
  deriving Inhabited

def nImplicationOrder : Name := leanName ``Lean.Order.ImplicationOrder
def nReverseImplicationOrder : Name := leanName ``Lean.Order.ReverseImplicationOrder

/-- `ImplicationOrder` and `ReverseImplicationOrder` (both `:= Prop`) read
as `Prop`. The lattice-theoretic fixpoints spell a component type
`∀ x, ImplicationOrder` where the packed constant's type says `∀ x, Prop`
(the functional's binder takes its type from the instances, `Meta/Order.lean`
and `PartialFixpoint/Main.lean`), so the clique's packing is recognised up to
the alias; each occurrence keeps its own spelling when it is rebuilt. -/
def normOrderAlias : Expr → Expr
  | e@(.const c _ _) =>
    if c == nImplicationOrder || c == nReverseImplicationOrder then Expr.mkSort Level.mkZero else e
  | .app f a _ => Expr.mkApp (normOrderAlias f) (normOrderAlias a)
  | .lam n t b bi _ => Expr.mkLam n (normOrderAlias t) (normOrderAlias b) bi
  | .forallE n t b bi _ => Expr.mkForallE n (normOrderAlias t) (normOrderAlias b) bi
  | .mdata _ x _ => normOrderAlias x
  | e => e

def PFLayout.isClique (L : PFLayout) (s : Spine) : Bool :=
  s.size == L.n && (matchPackingLeaves (s.leaves.map normOrderAlias)
    (L.leaves.map normOrderAlias)).isSome

/-- The `toPartialOrder` of a `CCPO`/`CompleteLattice` instance. -/
def toPO (lattice : Bool) (lvl : Level) (ty inst : Expr) : Expr :=
  mkAppN (Expr.mkConst (if lattice then nLatticeToPO else nCCPOToPO) #[lvl]) #[ty, inst]

/-- The order data of a clique, read off `toPartialOrder γ I`: the packed
type, Lean's spine, the leaf instances and the instance kind. -/
structure OrderData where
  /-- the packing as the instances spell it -/
  spine : Spine
  insts : Array Expr
  lattice : Bool
  /-- the packing as the component types spell it: the same as `spine`
  for a CCPO; for the lattice-theoretic fixpoints `∀ x, Prop` where the
  instances say `∀ x, ImplicationOrder`. Lean uses each spelling at fixed
  positions: the component types (the codomain of the monotonicity
  statement, `monotone_mk`'s `α`, `β` and their orders) and the domain of a
  path proof (`monotone_fst`'s `γ`, the functions' binders, `monotone_id`)
  take this one; the instances, the packed order and a path's nodes the
  other. -/
  tspine : Spine
  deriving Inhabited

def decodeOrderData (L : PFLayout) (po : Expr) : Option OrderData := do
  let (h, _, args) ← constApp? po
  unless (h == nCCPOToPO || h == nLatticeToPO) && args.size == 2 do none
  let (ih, s, insts) ← decodeInstTree L.n args[1]!
  unless L.isClique s do none
  some { spine := s, insts, lattice := ih == nInstLatticePProd, tspine := s }

/-- `toPartialOrder γ I`. -/
def OrderData.packedPO (d : OrderData) : Expr :=
  let suf := d.spine.suffixes
  toPO d.lattice (suf[0]!).2 d.spine.type
    (mkInstTree (if d.lattice then nInstLatticePProd else nInstCCPOPProd) d.spine d.insts)

/-- The partial order of suffix `k` as `whnfUntil … instPartialOrderPProd`
leaves it: `toPartialOrder S_k I_k`. -/
def OrderData.suffixPO (d : OrderData) (k : Nat) : Expr :=
  let suf := d.spine.suffixes
  let n := d.spine.size
  let inst := if k + 1 == n then d.insts[n-1]! else
    mkInstTree (if d.lattice then nInstLatticePProd else nInstCCPOPProd)
      { d.spine with leaves := d.spine.leaves.extract k n, lvls := d.spine.lvls.extract k n }
      (d.insts.extract k n)
  toPO d.lattice (suf[k]!).2 (suf[k]!).1 inst

/-- The `instPartialOrderPProd` tree of suffix `k` (the codomain order of
`monotone_mk`'s statement). -/
def OrderData.poTree (d : OrderData) (k : Nat) : Expr :=
  let t := d.tspine
  let n := t.size
  let leafPO (j : Nat) := toPO d.lattice t.lvls[j]! t.leaves[j]! d.insts[j]!
  if k + 1 == n then leafPO (n - 1) else
  mkInstTree nInstPOPProd
    { t with leaves := t.leaves.extract k n, lvls := t.lvls.extract k n }
    ((List.range (n - k)).toArray.map fun j => leafPO (k + j))

def OrderData.permute (d : OrderData) (σ : Array Nat) : OrderData :=
  { d with spine := d.spine.permute σ, insts := Ix.Compile.Clique.permute σ d.insts,
           tspine := d.tspine.permute σ }

/-! ## (G): `solveMonoCall`'s path proofs -/

/-- The monotonicity proof of `λ x. x.π_j` (`solveMonoCall` on the path,
inside out): `monotone_id`, then `monotone_snd` per `.2`, `monotone_fst` for
the final `.1`. Returns the proof and the function it is about. -/
def mkPathProof (d : OrderData) (j : Nat) : Expr × Expr := Id.run do
  let s := d.spine
  let n := s.size
  let suf := s.suffixes
  -- the domain as the component types spell it
  let γ := d.tspine.type
  let lγ := (suf[0]!).2
  let poγ := d.packedPO
  let xName := Ix.Name.mkStr Ix.Name.mkAnon "x"
  let mut f := Expr.mkLam xName γ (Expr.mkBVar 0) .default
  let mut h := mkAppN (Expr.mkConst nMonoId #[lγ]) #[γ, poγ]
  let mut body := Expr.mkBVar 0
  let steps : Array (Nat × Bool) :=
    (List.range j).toArray.map (fun k => (k, false)) ++ (if j + 1 < n then #[(j, true)] else #[])
  for (k, isFst) in steps do
    let (r, lr) := suf[k+1]!
    let leafPO := toPO d.lattice s.lvls[k]! s.leaves[k]! d.insts[k]!
    let restPO := d.suffixPO (k + 1)
    let lem := if isFst then nMonoFst else nMonoSnd
    h := mkAppN (Expr.mkConst lem #[s.lvls[k]!, lr, lγ]) #[s.leaves[k]!, r, γ, leafPO, restPO, poγ, f, h]
    let proj := if isFst then nPProdFst else nPProdSnd
    body := mkAppN (Expr.mkConst proj #[s.lvls[k]!, lr]) #[s.leaves[k]!, r, body]
    f := Expr.mkLam xName γ body .default
  return (h, f)

/-- Decode a `monotone_fst`/`monotone_snd` chain: the order data and the
component; checked by regenerating it with Lean's order. -/
def decodePathProof (L : PFLayout) (e : Expr) : Option (OrderData × Nat) := do
  let (h, _, args) ← constApp? e
  unless (h == nMonoFst || h == nMonoSnd || h == nMonoId) do none
  let po ← if h == nMonoId then (if args.size == 2 then args[1]? else none)
    else (if args.size == 8 then args[5]? else none)
  let d ← decodeOrderData L po
  -- the domain's spelling
  let dom ← if h == nMonoId then args[0]? else args[2]?
  let ts ← decodeSpine .pprod L.n dom
  unless L.isClique ts do none
  let d := { d with tspine := ts }
  -- count the steps
  let mut cur := e
  let mut snds := 0
  let mut fst := false
  for _ in [0:L.n] do
    match constApp? cur with
    | some (h', _, args') =>
      if h' == nMonoSnd && args'.size == 8 then snds := snds + 1; cur := args'[7]!
      else if h' == nMonoFst && args'.size == 8 then
        if fst || snds > 0 then none
        fst := true; cur := args'[7]!
      else break
    | none => break
  let j := snds
  unless (fst && j + 1 < L.n) || (!fst && j + 1 == L.n) do none
  if alphaEq (mkPathProof d j).1 e then some (d, j) else none

/-! ## The `monotone_mk` tree -/

/-- `PProd.monotone_mk` over the per-function proofs (`mkMonoPProd` folded
from the right): `fs` the functionals `F_k` (each `λ x. …`), `hs` their
proofs. -/
def mkMonoTreeOver (γ : Expr) (lγ : Level) (poγ : Expr) (d : OrderData) (fs hs : Array Expr) :
    Expr := Id.run do
  -- the components as their types spell them
  let s := d.tspine
  let n := s.size
  let suf := s.suffixes
  let xName := Ix.Name.mkStr Ix.Name.mkAnon "x"
  -- `g` for the rest from `k`: `F_{n-1}`, or `λ x. ⟨F_k[x], g_{k+1}[x]⟩`
  let instBody (f : Expr) : Expr := match stripMdata f with
    | .lam _ _ b _ _ => b
    | f => Expr.mkApp (liftLoose f 1) (Expr.mkBVar 0)
  let mut g := fs[n-1]!
  let mut h := hs[n-1]!
  for k in (List.range (n - 1)).reverse do
    let (r, lr) := suf[k+1]!
    let leafPO := toPO d.lattice s.lvls[k]! s.leaves[k]! d.insts[k]!
    h := mkAppN (Expr.mkConst nMonoMk #[s.lvls[k]!, lr, lγ])
      #[s.leaves[k]!, r, γ, leafPO, d.poTree (k + 1), poγ, fs[k]!, g, hs[k]!, h]
    if k > 0 then
      let tup := mkAppN (Expr.mkConst nPProdMk #[s.lvls[k]!, lr])
        #[liftLoose s.leaves[k]! 1, liftLoose r 1, instBody fs[k]!, instBody g]
      g := Expr.mkLam xName γ tup .default
  return h

/-- The `monotone_mk` tree of a fixpoint, over its own packed type. -/
def mkMonoTree (d : OrderData) (fs hs : Array Expr) : Expr :=
  mkMonoTreeOver d.spine.type (d.spine.suffixes[0]!).2 d.packedPO d fs hs

/-- The composition fallback of §5.2 for the per-function proof `h : monotone F`
(Lean's, over Lean's packing `d`): `monotone_compose (mono φ) h`, a proof of
`monotone (λ y. F (φ y))`, which is `monotone F'` by β and projection of a
constructor (`F'` the transported functional), where `φ : γ' → γ` is
`y ↦ ⟨y.π'_{σ 0}, …⟩` and `mono φ` a `monotone_mk` tree over regenerated
path proofs (G). `compose?` gives `monotone_compose`'s universe parameters. -/
def mkComposeFallback (σ : Array Nat) (d d' : OrderData) (k : Nat) (F h : Expr)
    (composeLevels : Array Name) : Except String Expr := do
  let s := d.spine
  let n := s.size
  let γ' := d'.spine.type
  let lγ' := (d'.spine.suffixes[0]!).2
  let γ := s.type
  let lγ := (s.suffixes[0]!).2
  let yName := Ix.Name.mkStr Ix.Name.mkAnon "y"
  -- φ = λ y. ⟨y.π'_{σ 0}, …⟩ over Lean's packing
  let lifted : Spine := { s with leaves := s.leaves.map (liftLoose · 1) }
  let lifted' : Spine := { d'.spine with leaves := d'.spine.leaves.map (liftLoose · 1) }
  let comps := (List.range n).toArray.map fun i => mkPathApp lifted' σ[i]! (Expr.mkBVar 0)
  let φ := Expr.mkLam yName γ' (mkTuple lifted comps) .default
  -- mono φ: the component functions and their path proofs
  let paths := (List.range n).toArray.map fun i => mkPathProof d' σ[i]!
  let monoφ := mkMonoTreeOver γ' lγ' d'.packedPO d (paths.map (·.2)) (paths.map (·.1))
  let poD := toPO d.lattice s.lvls[k]! s.leaves[k]! d.insts[k]!
  let lvl (nm : Name) : Except String Level :=
    if nm == Ix.Name.mkStr Ix.Name.mkAnon "u" then pure lγ'
    else if nm == Ix.Name.mkStr Ix.Name.mkAnon "v" then pure lγ
    else if nm == Ix.Name.mkStr Ix.Name.mkAnon "w" then pure s.lvls[k]!
    else throw "monotone_compose: unexpected universe parameter"
  let us ← composeLevels.mapM lvl
  return mkAppN (Expr.mkConst nMonoCompose us)
    #[γ', d'.packedPO, γ, d.packedPO, s.leaves[k]!, poD, φ, F, monoφ, h]

/-- Decode a `monotone_mk` tree over the clique's packing, checked by
re-encoding. -/
def decodeMonoTree (L : PFLayout) (e : Expr) : Option (OrderData × Array Expr × Array Expr) := do
  let (h, _, args) ← constApp? e
  unless h == nMonoMk && args.size == 10 do none
  let d ← decodeOrderData L args[5]!
  -- the components' spelling, from the outermost node's `α` and `β`
  let (_, us, _) ← constApp? e
  let ts ← decodeSpine .pprod L.n
    (mkNode .pprod (us[0]?.getD Level.mkZero) (us[1]?.getD Level.mkZero) args[0]! args[1]!)
  unless L.isClique ts do none
  let d := { d with tspine := ts }
  let mut fs := #[]
  let mut hs := #[]
  let mut cur := e
  for _ in [0:L.n-1] do
    match constApp? cur with
    | some (h', _, args') =>
      unless h' == nMonoMk && args'.size == 10 do none
      fs := fs.push args'[6]!; hs := hs.push args'[8]!
      if fs.size + 1 == L.n then fs := fs.push args'[7]!; hs := hs.push args'[9]!
      cur := args'[9]!
    | none => none
  unless fs.size == L.n do none
  if alphaEq (mkMonoTree d fs hs) e then some (d, fs, hs) else none

/-! ## User-written monotonicity proofs

`solveMono`'s proofs (`Elab/Tactic/Monotonicity.lean`) are compositions of
the `monotone_*` lemmas whose only binders are the functionals' packed
variable (`λ x : γ. …`) and the functions' own arguments: the order on the
packing is never unfolded. A per-function proof that binds a variable whose
type mentions the packing in any other way (`h : f ⊑ g` after `intro f g h`,
an `And` over the packing, whose projections `h.1`, `h.2` select factors by
position) was written against Lean's packing in a way the grammar cannot see;
it takes the composition fallback (§5.2). -/

/-- Some subterm of `e` is the clique's packed type (any spelling of its
leaves). -/
def mentionsPacking (L : PFLayout) (e : Expr) : Bool := (go e).run' {}
where
  go (e : Expr) : StateM (Std.HashSet Expr) Bool := do
    if (← get).contains e then return false
    modify (·.insert e)
    let here : Bool := match decodeSpine .pprod L.n e with
      | some s => L.isClique s
      | none => false
    if here then return true
    match e with
    | .app f a _ => return (← go f) || (← go a)
    | .lam _ t b _ _ | .forallE _ t b _ _ => return (← go t) || (← go b)
    | .letE _ t v b _ _ => return (← go t) || (← go v) || (← go b)
    | .proj _ _ x _ | .mdata _ x _ => go x
    | _ => return false

/-- `some why` when a per-function monotonicity proof binds a variable whose
type mentions the packing other than as the packed type itself. -/
def userProofCheck (L : PFLayout) (e : Expr) : Option String := (go e).run' {}
where
  isPacked (t : Expr) : Bool := match decodeSpine .pprod L.n (stripMdata t) with
    | some s => L.isClique s
    | none => false
  bad (t : Expr) : Bool := !isPacked t && mentionsPacking L t
  go (e : Expr) : StateM (Std.HashSet Expr) (Option String) := do
    if (← get).contains e then return none
    modify (·.insert e)
    match e with
    | .lam _ t b _ _ | .forallE _ t b _ _ =>
      if bad t then return some "grammar: a binder whose type mentions the packing (a user-written monotonicity proof)"
      match ← go t with
      | some w => return some w
      | none => go b
    | .letE _ t v b _ _ =>
      if bad t then return some "grammar: a let whose type mentions the packing (a user-written monotonicity proof)"
      match ← go t with
      | some w => return some w
      | none => match ← go v with
        | some w => return some w
        | none => go b
    | .app f a _ =>
      match ← go f with
      | some w => return some w
      | none => go a
    | .proj _ _ x _ | .mdata _ x _ => go x
    | _ => return none

/-! ## `Φ_σ` -/

def phiPFStep (L : PFLayout) (go : Array Expr → Expr → TM Expr) (ctx : Array Expr) (e : Expr) :
    TM Expr := do
  let goD (d : OrderData) : TM OrderData := do
    let leaves ← d.spine.leaves.mapM (go ctx)
    let tleaves ← d.tspine.leaves.mapM (go ctx)
    let insts ← d.insts.mapM (go ctx)
    return ({ d with spine := { d.spine with leaves }, insts,
                     tspine := { d.tspine with leaves := tleaves } }).permute L.sigma
  let isPackedTy (ty : Expr) : Bool := match decodeSpine .pprod L.n ty with
    | some s => L.isClique s
    | none => false
  -- the recognised constructs
  if let some (d, j) := decodePathProof L e then
    let d' ← goD d
    return (mkPathProof d' L.sigma[j]!).1
  if let some (d, fs, hs) := decodeMonoTree L e then
    let d' ← goD d
    let fs' ← fs.mapM (go ctx)
    let mut hs' := #[]
    for k in [0:L.n] do
      let st ← get
      let attempt : TM Expr := do
        if let some why := userProofCheck L hs[k]! then throw why
        go ctx hs[k]!
      match attempt.run st with
      | .ok (h, st') => set st'; hs' := hs'.push h
      | .error err =>
        -- outside the grammar: the composition fallback (§5.2)
        let h ← liftE (mkComposeFallback L.sigma d d' k fs[k]! hs[k]! L.composeLevels)
        modify fun st => { st with fallbacks := st.fallbacks.push s!"monotonicity proof {k}: {err}" }
        hs' := hs'.push h
    return mkMonoTree d' (permute L.sigma fs') (permute L.sigma hs')
  -- a path proof over the packing that is not `solveMonoCall`'s (a user's
  -- lemma chain, with other instances): outside the grammar
  if let some (c, _, args) := constApp? e then
    if (c == nMonoFst || c == nMonoSnd) && args.size ≥ 8 && isPackedTy args[2]! then
      throw "grammar: a monotone_fst/monotone_snd chain over the packing that is not solveMonoCall's"
    if c == nMonoId && args.size ≥ 2 && isPackedTy args[0]! then
      throw "grammar: monotone_id over the packing outside a path proof"
  if let some (h, s, insts) := decodeInstTree L.n e then
    if L.isClique s then
      let leaves ← s.leaves.mapM (go ctx)
      let insts ← insts.mapM (go ctx)
      return mkInstTree h ({ s with leaves }.permute L.sigma) (permute L.sigma insts)
  if let some (s, j, base) := decodePathApp L.n e then
    if L.isClique s then
      let leaves ← s.leaves.mapM (go ctx)
      return mkPathApp ({ s with leaves }.permute L.sigma) L.sigma[j]! (← go ctx base)
  if let some (s, cs) := decodeTuple L.n e then
    if L.isClique s then
      let leaves ← s.leaves.mapM (go ctx)
      let cs ← cs.mapM (go ctx)
      return mkTuple ({ s with leaves }.permute L.sigma) (permute L.sigma cs)
  if let some s := decodeSpine .pprod L.n e then
    if L.isClique s then
      let leaves ← s.leaves.mapM (go ctx)
      return ({ s with leaves }.permute L.sigma).type
  match e with
  | .proj .. =>
    let (steps, base) := projChain e
    let packedBase : Bool := match stripMdata base with
      | .bvar i _ => if h : i < ctx.size then isPackedTy (liftLoose ctx[ctx.size - 1 - i] (i + 1))
          else false
      | b => match constApp? b with
        | some (c, _, _) => c == L.packedName
        | none => false
    let b ← go ctx base
    if packedBase then
      let some (idx, len) := pathPrefix L.n steps | throw "grammar: a projection of the packed value that is not a path"
      let canon := L.spine.permute L.sigma
      unless stepsFit L.spine idx (steps.extract 0 len) do
        throw "grammar: a path whose projections are not the packing's"
      return applyProjs (canon.projSteps L.sigma[idx]! ++ steps.extract len steps.size) b
    return applyProjs steps b
  | .app .. =>
    let (h, args) := getAppFnArgs e
    if let .const c us _ := h then
      if c == L.packedName then
        if args.size < L.numFixed then throw "grammar: a partial application of the packed fixpoint"
        let args' ← args.mapM (go ctx)
        return mkAppN (Expr.mkConst L.newPackedName us)
          (L.fixedPerm.map (args'[·]!) ++ args'.extract L.numFixed args'.size)
      if let some ρ := L.proofPerm.get? c then
        if args.size < ρ.size then throw "grammar: a partial application of the monotonicity proof"
        let args' ← args.mapM (go ctx)
        return mkAppN h (ρ.map (args'[·]!) ++ args'.extract ρ.size args'.size)
      return mkAppN h (← args.mapM (go ctx))
    return mkAppN (← go ctx h) (← args.mapM (go ctx))
  | .const c us _ =>
    if c == L.packedName then
      if L.numFixed == 0 then return Expr.mkConst L.newPackedName us
      throw "grammar: a bare occurrence of the packed fixpoint"
    return e
  | .lam nm t b bi _ => return Expr.mkLam nm (← go ctx t) (← go (ctx.push t) b) bi
  | .forallE nm t b bi _ => return Expr.mkForallE nm (← go ctx t) (← go (ctx.push t) b) bi
  | .letE nm t v b nd _ => return Expr.mkLetE nm (← go ctx t) (← go ctx v) (← go (ctx.push t) b) nd
  | .mdata d x _ => return Expr.mkMData d (← go ctx x)
  | _ => return e

def phiPFFix (L : PFLayout) : Nat → Array Expr → UInt64 → Expr → TM Expr
  | 0, _, _, _ => throw "Φ: recursion bound exhausted"
  | fuel + 1, ctx, hctx, e => do
    let key := mixHash (hash e) hctx
    if let some (e', ctx', r) := (← get).cacheCtx.get? key then
      if e' == e && ctx' == ctx then return r
    let go (ctx' : Array Expr) (x : Expr) : TM Expr :=
      phiPFFix L fuel ctx' (ctx'.foldl (fun h t => mixHash h (hash t)) 7) x
    let r ← phiPFStep L go ctx e
    modify fun st => { st with cacheCtx := st.cacheCtx.insert key (e, ctx, r) }
    return r

def phiPF (L : PFLayout) (ctx : Array Expr) (e : Expr) : TM Expr :=
  phiPFFix L defaultFuel ctx (ctx.foldl (fun h t => mixHash h (hash t)) 7) e

/-- The layout from the members (Lean's order) and the packed fixpoint. -/
def pfLayout (members : Array Decl) (packed : Decl) (σ : Array Nat) (newPackedName : Name) :
    Except String PFLayout := do
  let n := members.size
  unless n ≥ 2 && σ.size == n && isPerm σ do throw "pfLayout: bad permutation"
  let m := Ix.Compile.Image.forallArity packed.type
  let (_, γ) := peelForalls m packed.type #[]
  let some s := decodeSpine .pprod n γ | throw "pfLayout: the packed type is not Lean's PProd packing"
  -- each member projects its own component of `f₀.mutual fixed`
  let mut qss : Array (Array Nat) := #[]
  for i in [0:n] do
    let d := members[i]!
    let (ps, body) := peelLams (lamArity d.value) d.value #[]
    let (h, _) := getAppFnArgs (stripMdata body)
    let (steps, base) := projChain h
    let some (c, _, args) := constApp? base | throw s!"pfLayout: member {i} is not a projection of the fixpoint"
    unless c == packed.name && args.size == m do throw s!"pfLayout: member {i} is not a projection of the fixpoint"
    match pathPrefix n steps with
    | some (j, len) => unless j == i && len == steps.size do throw s!"pfLayout: member {i} projects component {j}"
    | none => throw s!"pfLayout: member {i}: not a path"
    let mut qs := #[]
    for a in args do
      match stripMdata a with
      | .bvar b _ => if b < ps.size then qs := qs.push (ps.size - 1 - b) else throw "pfLayout: fixed argument"
      | _ => throw "pfLayout: a fixed argument is not a parameter"
    unless qs.toList.eraseDups.length == qs.size do
      throw "pfLayout: distinct fixed parameters alias the same member binder"
    qss := qss.push qs
  unless qss[0]! == qss[0]!.qsort (· < ·) do
    throw "pfLayout: the fixed parameters are not in the first member's order"
  let qg := qss[(invPerm σ)[0]!]!
  let fixedPerm := (idPerm m).qsort fun a b => qg[a]! < qg[b]!
  return { n, sigma := σ, packedName := packed.name, newPackedName, numFixed := m, fixedPerm,
           leaves := s.leaves, spine := s, memberFixed := qss }

/-- Historical shape-based route, retained for the value-changing audit
controls. Production uses `PFConjugation.transportPF`. -/
def transportPFShape (members : Array Decl) (packed : Decl) (proofs : Array Decl) (σ : Array Nat)
    (newPackedName : Name) (const? : Name → Option ConstantInfo)
    (lemmas : Array (Decl × Name) := #[]) : TM WFOutput := do
  let L ← liftE (pfLayout members packed σ newPackedName)
  let composeLevels := match const? nMonoCompose with
    | some ci => ci.getCnst.levelParams
    | none => #[]
  let L := { L with composeLevels }
  let m := L.numFixed
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun s p => s.insert p.name
  let (xs, body) ← openBinders true m packed.value
  let uses := scanProofs proofNames (xs.map (·.fvar)) body {}
  let inv := invPerm L.fixedPerm
  let proofPerm : Std.HashMap Name (Array Nat) := uses.fold (init := {}) fun acc c js =>
    acc.insert c ((idPerm js.size).qsort fun a b => inv[js[a]!]! < inv[js[b]!]!)
  let L := { L with proofPerm }
  let phi (e : Expr) : TM Expr := phiPF L #[] e
  let value ← withReorderedBinders true m L.fixedPerm packed.value phi
  let type ← withReorderedBinders false m L.fixedPerm packed.type phi
  let mut out : Array Transported := #[{ decl := { packed with name := newPackedName, type, value } }]
  for p in proofs do
    let ρ := (proofPerm.get? p.name).getD #[]
    let type ← withReorderedBinders false ρ.size ρ p.type phi
    let before := (← get).fallbacks.size
    let value ← withReorderedBinders true ρ.size ρ p.value phi
    let fb := (← get).fallbacks.extract before (← get).fallbacks.size
    out := out.push { decl := { p with type, value },
                      fallback := if fb.isEmpty then none else some ("; ".intercalate fb.toList) }
  for d in members do
    out := out.push { decl := { d with type := ← phi d.type, value := ← phi d.value } }
  -- the carried equation lemmas (a failure leaves the clique in Lean's form)
  for (d, nn) in lemmas do
    out := out.push { decl := { d with name := nn, type := ← phi d.type, value := ← phi d.value } }
  -- (R): the proofs follow the packed fixpoint's name
  let order := constOccurrences proofNames.contains value
  let rest := (proofs.map (·.name)).filter fun p => !order.contains p
  let numbered := (order ++ rest).zipIdx.map fun (p, i) =>
    (p, Ix.Name.mkStr newPackedName s!"_proof_{i + 1}")
  let lemmaRenames := lemmas.filterMap fun (d, nn) => if d.name != nn then some (d.name, nn) else none
  let rn : Std.HashMap Name Name := (numbered ++ lemmaRenames).foldl (init := {}) fun m (a, b) => m.insert a b
  let out2 := out.map fun t =>
    { t with decl := { t.decl with name := (rn.get? t.decl.name).getD t.decl.name
                                   type := renameConsts rn.get? t.decl.type
                                   value := renameConsts rn.get? t.decl.value } }
  return { decls := out2, renames := #[(packed.name, newPackedName)] ++ numbered ++ lemmaRenames }

end Ix.Compile.Clique

end
