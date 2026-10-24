/-
  Ix.Compile.Pass.Clique.WF: the layout of a well-founded clique and the
  helpers of its transport.

  Lean's encoding (`Elab/PreDefinition/WF`, Lean 4.34.1):

  * `f₀._mutual : ∀ fixed, (x : α) → C x` with `α = PSum D₀ (… D_{n-1})` in
    Lean's clique order and `C` a `mkCodomain` case tree; the fixed
    parameters in the first function's order;
  * its value `λ fixed. WellFounded.fix α (λ x. C x) rel wf F` or
    `λ fixed. WellFounded.Nat.fix α (λ x. C x) measure F`, where `rel`
    (`(invImage m inst).1`) and `measure` carry the per-function measures in a
    case tree over `α`, and `F = λ x a. tree` is `processSumCasesOn`'s
    refinement tree whose leaves are the functions' bodies, recursive calls
    `a (inj_j ⟨args⟩) h`;
  * the decreasing proofs `f₀._mutual._proof_k : ∀ ctx, rel (inj_j y) (inj_i x)`
    (definitions; for theorems they stay inline), whose bodies mention the
    packing in copies of their goal (`id`, motives);
  * the members `f_i := λ ps. f₀._mutual fixed (inj_i ⟨varying⟩)`.

  This file holds the layout (`wfLayout`: the clique's packing, the fixed
  parameters and their permutation), the proofs' fixed-argument scan, the
  prologue and epilogue the well-founded and `partial_fixpoint` transports
  share (`fixedProofPerms`, `numberProofs`), and the pieces of the packed
  equation lemma's regeneration. The transport itself finds the encoding by
  ownership, from the root of `f₀._mutual` (`WFSchema.lean`,
  `WFConjugation.lean`, `WFMatcher.lean`); it never recognises the packing by
  its shape elsewhere in a term, so user values of the packing's type are
  left alone.
-/
module
public import Ix.Compile.Pass.Clique.Packing
public import Ix.Compile.Pass.Clique.PackingMatch
public import Ix.Compile.Pass.Clique.Telescope
@[expose] public section

namespace Ix.Compile.Pass.Clique

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata peelForalls)
open Ix.Compile.Image (Local forallArity)

/-- What `Φ_σ` needs to know about a well-founded clique. -/
structure WFLayout where
  n : Nat
  /-- Lean index ↦ canonical position -/
  sigma : Array Nat
  mutualName : Name
  newMutualName : Name
  numFixed : Nat
  /-- new fixed position `p` ↦ Lean's fixed position -/
  fixedPerm : Array Nat
  /-- Lean's summands `D_i`, from `f₀._mutual`'s type (the fixed parameters as
  loose variables) -/
  leaves : Array Expr
  /-- abstracted proof ↦ the permutation of its leading fixed-parameter
  binders (empty when it uses none) -/
  proofPerm : Std.HashMap Name (Array Nat) := {}
  /-- the packed function's equation lemmas carried with the clique: in the
  user region, an application of one re-enters the encoding region at its
  packed argument, as an application of the packed function does -/
  packedLemmas : Std.HashSet Name := {}
  /-- per member (Lean's order): the member's parameter (outermost `0`) at
  each fixed position of its call of the packed function -/
  memberFixed : Array (Array Nat) := #[]
  deriving Inhabited

def WFLayout.isClique (L : WFLayout) (s : Spine) : Bool :=
  s.size == L.n && (matchPackingLeaves s.leaves L.leaves).isSome

def nInvImage : Name := leanName ``InvImage
def nWFRelation : Name := leanName ``WellFoundedRelation

/-- The packing type of a spine inside the transport. A decoded spine (and
any permutation of one) always has it; a spine without leaves, or whose
leaves and levels differ in number, is a refusal named by `what`. -/
def Spine.typeM (s : Spine) (what : String) : TM Expr :=
  match s.type? with
  | some t => pure t
  | none => throw s!"{what}: the packing has no type (no leaves, or leaves and levels differ in number)"

/-- The indices of `keys` sorted by their key, equal keys in index order. The
order is total on `(key, index)`, so `qsort` returns the one sorted
arrangement, and the Rust twin's stable sort agrees with it. On distinct keys
this is the donor's `(idPerm keys.size).qsort fun i j => keys[i] < keys[j]`;
on equal keys (a proof that receives one fixed parameter twice) the donor's
unstable `qsort` order is replaced by index order. -/
def sortIdxByKey (keys : Array Nat) : Array Nat :=
  (keys.zipIdx.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).map (·.2)

/-! ## The layout -/

/-- The fixed-parameter positions of a member's call of `f₀._mutual`: for
each fixed argument, the member's parameter it is (outermost `0`). -/
def memberFixedArgs (mutualName : Name) (m : Nat) (member : Decl) :
    Except String (Array Nat × Expr) := do
  let (ps, body) := peelLams (lamArity member.value) member.value #[]
  let notPacked := s!"member {member.name}: not an application of the packed function"
  let some (h, _, args) := constApp? body | throw notPacked
  unless h == mutualName && args.size == m + 1 do throw notPacked
  let mut qs := #[]
  for j in [0:m] do
    let some arg := args[j]? | throw notPacked
    match stripMdata arg with
    | .bvar b _ =>
      if b < ps.size then qs := qs.push (ps.size - 1 - b)
      else throw s!"member {member.name}: fixed argument out of scope"
    | _ => throw s!"member {member.name}: a fixed argument is not a parameter"
  unless qs.toList.eraseDups.length == qs.size do
    throw s!"member {member.name}: distinct fixed parameters alias the same binder"
  let some packedArg := args[m]? | throw notPacked
  return (qs, packedArg)

def wfLayout (members : Array Decl) (mutDecl : Decl) (σ : Array Nat) (newMutualName : Name) :
    Except String WFLayout := do
  let n := members.size
  unless n ≥ 2 && σ.size == n && isPerm σ do throw "wfLayout: bad permutation"
  let ar := forallArity mutDecl.type
  unless ar ≥ 1 do throw "wfLayout: the packed function has no argument"
  let m := ar - 1
  let (bs, _) := peelForalls ar mutDecl.type #[]
  let some (_, α, _) := bs[m]? | throw "wfLayout: no packed argument"
  let some s := decodeSpine .psum n α | throw "wfLayout: the packed domain is not Lean's PSum packing"
  let mut qss : Array (Array Nat) := #[]
  for (member, i) in members.zipIdx do
    let (qs, arg) ← memberFixedArgs mutDecl.name m member
    match decodeInj n arg with
    | some (_, j, _) =>
      unless j == i do throw s!"wfLayout: member {i} injects at summand {j} (not Lean's order)"
    | none => throw s!"wfLayout: member {i}'s argument is not an injection"
    qss := qss.push qs
  -- Lean's fixed order is its first member's order
  let some q0 := qss[0]? | throw "wfLayout: bad permutation"
  unless q0 == q0.qsort (· < ·) do
    throw "wfLayout: the fixed parameters are not in the first member's order"
  -- the canonical first member's order
  let some inv := invPerm σ | throw "wfLayout: bad permutation"
  let some g := inv[0]? | throw "wfLayout: bad permutation"
  let some qg := qss[g]? | throw "wfLayout: bad permutation"
  -- `qg` has one entry per fixed position (`memberFixedArgs`)
  let fixedPerm := sortIdxByKey qg
  return { n, sigma := σ, mutualName := mutDecl.name, newMutualName, numFixed := m,
           fixedPerm, leaves := s.leaves, memberFixed := qss }

/-- For every application of an abstracted proof in the (opened) value of
`f₀._mutual`: the fixed parameters (by Lean position) among its leading
arguments, recorded at the first application met. The walk visits each
distinct subterm once, in first-occurrence pre-order (`foldDistinct`); an
application node is visited before its function part, so the full argument
list is the one recorded. -/
def scanProofs (proofs : Std.HashSet Name) (fixed : Array Name) (e : Expr)
    (initial : Std.HashMap Name (Array Nat)) : Std.HashMap Name (Array Nat) :=
  foldDistinct (init := initial) (e := e) fun acc x =>
    match x with
    | .app .. =>
      match getAppFnArgs x with
      | (.const c _ _, args) =>
        if proofs.contains c && !acc.contains c then
          let fixedIdx (a : Expr) : Option Nat := match stripMdata a with
            | .fvar y _ => fixed.idxOf? y
            | _ => none
          .yield (acc.insert c (args.toList.map fixedIdx |>.takeWhile Option.isSome
            |>.filterMap id).toArray)
        else .yield acc
      | _ => .yield acc
    | _ => .yield acc

/-! ## The transport's outcome, and the steps both packed transports share -/

/-- One constant's outcome. -/
structure Transported where
  decl : Decl
  /-- `none`: transported; `some why`: Lean's term kept (the faithful
  fallback), with the reason -/
  fallback : Option String := none
  deriving Inhabited

/-- The outcome of a packed transport (well-founded or `partial_fixpoint`). -/
structure TransportOutput where
  decls : Array Transported
  /-- Lean's constant ↦ its canonical name (the packed function, the
  renumbered proofs, the renamed lemmas) -/
  renames : Array (Name × Name)

/-- The abstracted proofs' fixed parameters, as both packed transports
compute them before transporting anything (`fixedProofPerms`). -/
structure FixedProofs where
  /-- the abstracted proofs' names -/
  proofNames : Std.HashSet Name
  /-- the packed function's fixed parameters, opened with fresh free
  variables (Lean's order) -/
  fixed : Array Local
  /-- the packed function's value under them -/
  body : Expr
  /-- proof ↦ the fixed parameters (Lean position) among the leading
  arguments of its first application in `body` (`scanProofs`) -/
  uses : Std.HashMap Name (Array Nat)
  /-- proof ↦ the permutation of its leading fixed-parameter binders: their
  indices sorted by the new position of the fixed parameter each one is -/
  proofPerm : Std.HashMap Name (Array Nat)

/-- The prologue of the packed transports (`transportWF`, `transportPF`):
open the `numFixed` fixed parameters of the packed function's value
`packedValue` (allocating their free variables), scan the abstracted
`proofs`' applications for the fixed parameters they receive, and order each
proof's leading fixed binders by the new fixed order `fixedPerm` (new
position ↦ Lean's position). `fixedPerm` not being a permutation of the
fixed positions, or a recorded position outside it, is a refusal (neither
happens for a layout's own permutation). -/
def fixedProofPerms (proofs : Array Decl) (numFixed : Nat) (fixedPerm : Array Nat)
    (packedValue : Expr) : TM FixedProofs := do
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun names proof => names.insert proof.name
  let (fixed, body) ← openBinders true numFixed packedValue
  let uses := scanProofs proofNames (fixed.map (·.fvar)) body {}
  let some inverse := invPerm fixedPerm
    | throw "clique transport: the fixed-parameter order is not a permutation"
  let proofPerm ← uses.foldM (init := ({} : Std.HashMap Name (Array Nat))) fun acc name positions => do
    let some keys := positions.mapM (inverse[·]?)
      | throw s!"clique transport: proof {name} receives a fixed parameter outside the fixed order"
    return acc.insert name (sortIdxByKey keys)
  return { proofNames, fixed, body, uses, proofPerm }

/-- The epilogue of the packed transports (`transportWF`, `transportPF`):
number the abstracted `proofs` `newName._proof_{i+1}`, first those the
transported packed value `value` mentions, in first-occurrence order
(`constOccurrences`), then the others in `proofs` order; rename each carried
lemma `(lemma, name)` whose name changes; apply both renamings to the name,
type and value of every declaration of `output`; and list the renames, the
packed function `packedName ↦ newName` first, then the proofs, then the
lemmas. -/
def numberProofs (output : Array Transported) (packedName newName : Name)
    (proofs : Array Decl) (lemmas : Array (Decl × Name)) (value : Expr) : TransportOutput :=
  let proofNames : Std.HashSet Name := proofs.foldl (init := {}) fun names proof => names.insert proof.name
  let used := constOccurrences proofNames.contains value
  let rest := (proofs.map (·.name)).filter fun name => !used.contains name
  let numbered := (used ++ rest).zipIdx.map fun (name, index) =>
    (name, Ix.Name.mkStr newName s!"_proof_{index + 1}")
  let lemmaRenames := lemmas.filterMap fun (declaration, name) =>
    if declaration.name != name then some (declaration.name, name) else none
  let names : Std.HashMap Name Name := (numbered ++ lemmaRenames).foldl (init := {})
    fun names (old, new) => names.insert old new
  let renamed := output.map fun item => { item with decl := { item.decl with
    name := (names.get? item.decl.name).getD item.decl.name
    type := renameConsts names.get? item.decl.type
    value := renameConsts names.get? item.decl.value } }
  { decls := renamed, renames := #[(packedName, newName)] ++ numbered ++ lemmaRenames }

/-! ## The packed function's equation lemma

Lean proves `f₀._mutual.eq_def : ∀ fixed x, f₀._mutual fixed x = T x` (the
case tree `T` of the bodies, recursive calls through `f₀._mutual`) by
`WellFounded.fix_eq` (or `Nat.fix_eq`) followed by a `simp` chain that
pushes the recursion argument through the case tree
(`PSum.casesOn._arg_pusher`, `congrArg PSum.rec`, …). That chain's shape
follows the packing node by node and is not transported. The canonical lemma
keeps the transported statement, keeps Lean's `fix_eq` step, and replaces the
chain by the step it computes, made explicit: a case split on the packed
argument (`PSum.casesOn` over the canonical packing, then `PSigma.casesOn`
over each summand's arguments), each leaf the `fix_eq` step at the
constructor. At a constructor, `f₀._mutual' fixed' (inj'_i ⟨a⃗⟩)` is
`fix … (inj'_i ⟨a⃗⟩)` by δ, and the functional applied to it reduces to the
statement's leaf by β and ι, so each leaf proves its case by conversion. The
proof is regenerated by a fixed term recipe; no tactic runs. The lemma exists
so that the members' own equation lemmas, transported with them, still prove
Lean's statements. -/

/-- `@id T p ↦ p`. -/
def stripId (e : Expr) : Expr :=
  match constApp? e with
  | some (h, _, #[_, p]) => if h == leanName ``id then p else e
  | _ => e

/-- The `fix_eq` step of Lean's packed equation lemma (the first argument of
its `Eq.trans`), opened at `xs` (the fixed parameters in Lean's order, then
the packed argument). -/
def eqDefFixStep (eqDef : Decl) (m : Nat) (xs : Array Expr) : Except String Expr := do
  let (bs, body) := peelLams (m + 1) eqDef.value #[]
  unless bs.size == m + 1 do throw "eq_def: the proof does not bind the fixed parameters and the argument"
  let body := instLocals body xs
  match constApp? (stripId body) with
  | some (h, _, #[_, _, _, _, step, _]) =>
    if h == leanName ``Eq.trans then return step
    else throw "eq_def: the proof is not `Eq.trans (fix_eq …) …`"
  | _ => throw "eq_def: the proof is not `Eq.trans (fix_eq …) …`"

/-- Split `major : ty` into its `PSigma` components and prove the motive at
`mk ⟨a⃗⟩` by `leaf`: `PSigma.casesOn` with motive `λ t. motive (mk t)` at each
`PSigma` level, `leaf (mk ⟨a⃗⟩)` at the atoms. `motive` and `leaf` may
refuse (they build injections, which can fail). -/
def splitPSigma (motive : Expr → TM Expr) (leaf : Expr → TM Expr) :
    Nat → Expr → (Expr → Expr) → Expr → TM Expr
  | 0, _, _, _ => throw "eq_def: PSigma nesting bound exhausted"
  | fuel + 1, ty, mk, major => do
    match constApp? ty with
    | some (h, us@#[u₀, u₁], #[α, β]) =>
      if h == nPSigma then
        let a ← freshFVar
        let b ← freshFVar
        let la : Local := { fvar := a, userName := Ix.Name.mkStr Ix.Name.mkAnon "a", type := α, bi := .default }
        let bty := (match stripMdata β with
          | .lam _ _ body _ _ => instantiateRev body #[Expr.mkFVar a]
          | _ => Expr.mkApp β (Expr.mkFVar a))
        let lb : Local := { fvar := b, userName := Ix.Name.mkStr Ix.Name.mkAnon "b", type := bty, bi := .default }
        let pair (t : Expr) : Expr :=
          mkAppN (Expr.mkConst (leanName ``PSigma.mk) us) #[α, β, Expr.mkFVar a, t]
        let inner ← splitPSigma motive leaf fuel bty (fun t => mk (pair t)) (Expr.mkFVar b)
        let t ← freshFVar
        let lt : Local := { fvar := t, userName := Ix.Name.mkStr Ix.Name.mkAnon "t", type := ty, bi := .default }
        let mot := mkLambda #[lt] (← motive (mk (Expr.mkFVar t)))
        return mkAppN (Expr.mkConst (leanName ``PSigma.casesOn) #[Level.mkZero, u₀, u₁])
          #[α, β, mot, major, mkLambda #[la, lb] inner]
      else leaf (mk major)
    | _ => leaf (mk major)

/-- `bvar d` occurs in `e` only as the head of an application (a recursive
call `a y h`), never passed on whole. -/
def onlyCalls : Nat → Nat → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, d, e@(.app ..) =>
    let (h, args) := getAppFnArgs e
    let headOk := match h with
      | .bvar _ _ => true
      | h => onlyCalls fuel d h
    headOk && args.all fun x => (match stripMdata x with
      | .bvar i _ => i != d
      | _ => true) && onlyCalls fuel d x
  | _, d, .bvar i _ => i != d
  | fuel + 1, d, .lam _ t b _ _ | fuel + 1, d, .forallE _ t b _ _ =>
    onlyCalls fuel d t && onlyCalls fuel (d + 1) b
  | fuel + 1, d, .letE _ t v b _ _ =>
    onlyCalls fuel d t && onlyCalls fuel d v && onlyCalls fuel (d + 1) b
  | fuel + 1, d, .proj _ _ x _ | fuel + 1, d, .mdata _ x _ => onlyCalls fuel d x
  | _, _, _ => true

/-- A leaf of the packed function's case tree (`λ v a. E`) whose recursion
variable reaches the bodies only through `PSigma.casesOn` layers (which the
regenerated proof splits) and is used there only as recursive calls: the
functional applied at a constructor then reduces to the statement's leaf by
β and ι. A body that threads the recursion variable through a `match`
(`MatcherApp.addArg`) needs Lean's argument pushing, which is not
regenerated. -/
def leafReduces : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    let (bs, body) := peelLams (lamArity e) e #[]
    if bs.isEmpty then false else
    match constApp? body with
    | some (h, _, #[_, _, _, _, minor, major]) =>
      if h == leanName ``PSigma.casesOn &&
          (match stripMdata major with
            | .bvar 0 _ => true
            | _ => false) then leafReduces fuel minor
      else onlyCalls transportFuel 0 body
    | _ => onlyCalls transportFuel 0 body

end Ix.Compile.Pass.Clique

end
