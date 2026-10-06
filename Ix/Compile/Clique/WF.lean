/-
  Ix.Compile.Clique.WF: the layout of a well-founded clique (design document
  §5.1) and the helpers of its transport.

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
  parameters and their permutation), the proofs' fixed-argument scan, and
  the pieces of the packed equation lemma's regeneration. The transport
  itself finds the encoding by ownership, from the root of `f₀._mutual`
  (`WFSchema.lean`, `WFConjugation.lean`, `WFMatcher.lean`). The earlier
  route that recognised the packing by its shape anywhere in a term
  (`recognise`, `isRelApp`, `phiWF`, `transportWFShape`) changed user values
  of the packing's type and is deleted; its miscompilations are kept as
  frozen data in `Tests/Ix/Compile/Recognition.lean`.
-/
module
public import Ix.Compile.Clique.Packing
public import Ix.Compile.Clique.PackingMatch
public import Ix.Compile.Clique.Telescope
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr)
open Ix.Compile.Canon (getAppFnArgs mkAppN liftLoose lowerLoose stripMdata peelForalls)
open Ix.Compile.Image (Local forallArity instLocals abstractFVars)

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

/-! ## The layout -/

/-- The fixed-parameter positions of a member's call of `f₀._mutual`: for
each fixed argument, the member's parameter it is (outermost `0`). -/
def memberFixedArgs (mutualName : Name) (m : Nat) (member : Decl) :
    Except String (Array Nat × Expr) := do
  let (ps, body) := peelLams (lamArity member.value) member.value #[]
  let some (h, _, args) := constApp? body
    | throw s!"member {member.name}: not an application of the packed function"
  unless h == mutualName && args.size == m + 1 do
    throw s!"member {member.name}: not an application of the packed function"
  let mut qs := #[]
  for j in [0:m] do
    match stripMdata args[j]! with
    | .bvar b _ =>
      if b < ps.size then qs := qs.push (ps.size - 1 - b)
      else throw s!"member {member.name}: fixed argument out of scope"
    | _ => throw s!"member {member.name}: a fixed argument is not a parameter"
  unless qs.toList.eraseDups.length == qs.size do
    throw s!"member {member.name}: distinct fixed parameters alias the same binder"
  return (qs, args[m]!)

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
  for i in [0:n] do
    let (qs, arg) ← memberFixedArgs mutDecl.name m members[i]!
    match decodeInj n arg with
    | some (_, j, _) =>
      unless j == i do throw s!"wfLayout: member {i} injects at summand {j} (not Lean's order)"
    | none => throw s!"wfLayout: member {i}'s argument is not an injection"
    qss := qss.push qs
  -- Lean's fixed order is its first member's order
  unless qss[0]! == (qss[0]!.qsort (· < ·)) do
    throw "wfLayout: the fixed parameters are not in the first member's order"
  -- the canonical first member's order
  let g := (invPerm σ)[0]!
  let qg := qss[g]!
  let fixedPerm := (idPerm m).qsort fun a b => qg[a]! < qg[b]!
  return { n, sigma := σ, mutualName := mutDecl.name, newMutualName, numFixed := m,
           fixedPerm, leaves := s.leaves, memberFixed := qss }

/-- For every application of an abstracted proof in the (opened) value of
`f₀._mutual`: the fixed parameters (by Lean position) among its leading
arguments. An application node is visited before its function part, so the
full argument list is the one recorded. -/
def scanProofs (proofs : Std.HashSet Name) (fixed : Array Name) :
    Expr → Std.HashMap Name (Array Nat) → Std.HashMap Name (Array Nat)
  | e@(.app f a _), acc =>
    let (h, args) := getAppFnArgs e
    let fixedIdx (x : Expr) : Option Nat := match stripMdata x with
      | .fvar y _ => fixed.idxOf? y
      | _ => none
    let acc := match h with
      | .const c _ _ =>
        if proofs.contains c && !acc.contains c then
          acc.insert c (args.toList.map fixedIdx |>.takeWhile Option.isSome
            |>.filterMap id).toArray
        else acc
      | _ => acc
    scanProofs proofs fixed a (scanProofs proofs fixed f acc)
  | .lam _ t b _ _, acc | .forallE _ t b _ _, acc =>
    scanProofs proofs fixed b (scanProofs proofs fixed t acc)
  | .letE _ t v b _ _, acc =>
    scanProofs proofs fixed b (scanProofs proofs fixed v (scanProofs proofs fixed t acc))
  | .proj _ _ x _, acc | .mdata _ x _, acc => scanProofs proofs fixed x acc
  | _, acc => acc

/-! ## The transport -/

/-- One constant's outcome. -/
structure Transported where
  decl : Decl
  /-- `none`: transported; `some why`: Lean's term kept (the faithful
  fallback), with the reason -/
  fallback : Option String := none
  deriving Inhabited

structure WFOutput where
  decls : Array Transported
  /-- Lean's constant ↦ its canonical name (the packed function, the
  renumbered proofs) -/
  renames : Array (Name × Name)

/-! ## The packed function's equation lemma (A5 proper)

Lean proves `f₀._mutual.eq_def : ∀ fixed x, f₀._mutual fixed x = T x` (the
case tree `T` of the bodies, recursive calls through `f₀._mutual`) by
`WellFounded.fix_eq` (or `Nat.fix_eq`) followed by a `simp` chain that
pushes the recursion argument through the case tree
(`PSum.casesOn._arg_pusher`, `congrArg PSum.rec`, …). That chain's shape
follows the packing node by node and is not transported. The canonical lemma
keeps the transported statement (S), keeps Lean's `fix_eq` step (Φ), and
replaces the chain by the step it computes, made explicit: a case split on
the packed argument (`PSum.casesOn` over the canonical packing, then
`PSigma.casesOn` over each summand's arguments), each leaf the `fix_eq` step
at the constructor. At a constructor, `f₀._mutual' fixed' (inj'_i ⟨a⃗⟩)` is
`fix … (inj'_i ⟨a⃗⟩)` by δ, and the functional applied to it reduces to the
statement's leaf by β and ι (§5.1's conversion steps), so each leaf proves
its case by conversion. This is regeneration (G) of a proof whose shape
depends on the packing, by a fixed term recipe; no tactic runs. Equation
lemmas are outside the canonicity claim (`LAZY`); the lemma exists so that
the members' own equation lemmas, transported with them, still prove
Lean's statements. -/

/-- `@id T p ↦ p`. -/
def stripId (e : Expr) : Expr :=
  match constApp? e with
  | some (h, _, args) => if h == leanName ``id && args.size == 2 then args[1]! else e
  | none => e

/-- The `fix_eq` step of Lean's packed equation lemma (the first argument of
its `Eq.trans`), opened at `xs` (the fixed parameters in Lean's order, then
the packed argument). -/
def eqDefFixStep (eqDef : Decl) (m : Nat) (xs : Array Expr) : Except String Expr := do
  let (bs, body) := peelLams (m + 1) eqDef.value #[]
  unless bs.size == m + 1 do throw "eq_def: the proof does not bind the fixed parameters and the argument"
  let body := instLocals body xs
  match constApp? (stripId body) with
  | some (h, _, args) =>
    if h == leanName ``Eq.trans && args.size == 6 then return args[4]!
    else throw "eq_def: the proof is not `Eq.trans (fix_eq …) …`"
  | none => throw "eq_def: the proof is not `Eq.trans (fix_eq …) …`"

/-- Split `major : ty` into its `PSigma` components and prove the motive at
`mk ⟨a⃗⟩` by `leaf`: `PSigma.casesOn` with motive `λ t. motive (mk t)` at each
`PSigma` level, `leaf (mk ⟨a⃗⟩)` at the atoms. -/
def splitPSigma (motive : Expr → Expr) (leaf : Expr → Expr) :
    Nat → Expr → (Expr → Expr) → Expr → TM Expr
  | 0, _, _, _ => throw "eq_def: PSigma nesting bound exhausted"
  | fuel + 1, ty, mk, major => do
    match constApp? ty with
    | some (h, us, #[α, β]) =>
      if h == nPSigma && us.size == 2 then
        let a ← freshFVar
        let b ← freshFVar
        let la : Local := { fvar := a, userName := Ix.Name.mkStr Ix.Name.mkAnon "a", type := α, bi := .default }
        let bty := (match stripMdata β with
          | .lam _ _ body _ _ => Ix.Compile.Canon.instantiateRev body #[Expr.mkFVar a]
          | _ => Expr.mkApp β (Expr.mkFVar a))
        let lb : Local := { fvar := b, userName := Ix.Name.mkStr Ix.Name.mkAnon "b", type := bty, bi := .default }
        let pair (t : Expr) : Expr :=
          mkAppN (Expr.mkConst (leanName ``PSigma.mk) us) #[α, β, Expr.mkFVar a, t]
        let inner ← splitPSigma motive leaf fuel bty (fun t => mk (pair t)) (Expr.mkFVar b)
        let t ← freshFVar
        let lt : Local := { fvar := t, userName := Ix.Name.mkStr Ix.Name.mkAnon "t", type := ty, bi := .default }
        let mot := Ix.Compile.Image.mkLambda #[lt] (motive (mk (Expr.mkFVar t)))
        return mkAppN (Expr.mkConst (leanName ``PSigma.casesOn) #[Level.mkZero, us[0]!, us[1]!])
          #[α, β, mot, major, Ix.Compile.Image.mkLambda #[la, lb] inner]
      else return leaf (mk major)
    | _ => return leaf (mk major)

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
    | some (h, _, args) =>
      if h == leanName ``PSigma.casesOn && args.size == 6 &&
          (match stripMdata args[5]! with
            | .bvar 0 _ => true
            | _ => false) then leafReduces fuel args[4]!
      else onlyCalls defaultFuel 0 body
    | none => onlyCalls defaultFuel 0 body

end Ix.Compile.Clique

end
