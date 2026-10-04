/- # The definitional passes: shared data (occurrence, block, recursor shape)

## Contract
Input: an *occurrence* `a.{us} args` of an image-kind auxiliary `a` of a
changed Lean block (design document §4.5), whose arguments are already in the
engine's normal form (the rewrite is bottom-up, `Ix.Compile.Pass.Translate`),
and the data of `a`'s block (`OptBlock`), built once per block rewrite from
Pass 1's canonical form and the images of Pass 3a:

* `change`: the block's change kind (Pass 1, `BlockCanon.change`): split,
  collapse, member reorder, nested order, evaporation;
* `classOf`: the canonical class of each member (Pass 1);
* `shapes`: for each Lean recursor `r` of the block, the **shape** of its
  generated image `img(r)` (Def 3.4), when it has one: the image is
  `λ ps ms mins is t. ρ.{ℓs} ps ms′ mins′ is t` with `ρ` an Ix recursor, the
  parameters, indices and major passed as the image's own variables in order,
  every Ix motive one of the image's motive variables (`motiveSrc`), and every
  Ix minor either one of the image's minor variables or another term (a
  relocated or wrapped minor, `minorSrc = none`). The shape is *read off the
  image*, so the motive and minor correspondence it records is exactly the
  one the image generator established by comparing motive types (§4.2 step 1);
* `ixRecInfo`, `resolves`: the Ix recursors' counts, and whether a name of an
  Ix auxiliary resolves in `E`.

Output: the classification of `a` (`AuxKind`, its recursor), the Ix auxiliary
of the same kind for a shape (`ixAuxOf`), and the permutation helpers the
passes use. No term is rewritten here.

## Faithfulness
Nothing is rewritten here. What the passes use: a shape is a syntactic fact
about `img(r)`; by Def 3.4 the image is definitionally Lean's recursor
(computation rules by `rfl`, `pass3` suite), so `r ps ms mins is t ≡
ρ.{ℓs} ps ms′ mins′ is t` by one δ-step (img) and β-steps (the arity), the
statement every pass builds on.

## Canonicity
A shape depends on the image, which depends on the canonical form and Lean's
recursor type only (Pass 3a); the Ix auxiliary names are the reserved display
names of the canonical positions (D14), resolved to addresses by `E`.

## Side condition and fallback
A missing shape, an unresolved Ix auxiliary or an arity that is not Lean's
standard telescope makes every pass that needs it decline; the occurrence then
keeps its baseline (the faithful form, §0.1).

## Non-canonical set and evidence
None of its own. Evidence: the per-pass fixtures (`Tests/Ix/Compile/Pass/`)
and the `pass3` suite's surgery comparison.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Block
public import Ix.Compile.Image.Expr
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevel BlockChange)

/-- An occurrence of an image-kind auxiliary: `head.{us} args`, the arguments
already in normal form. -/
structure Occ where
  head : Name
  us : Array Level
  args : Array Expr
  /-- The definition whose value contains the occurrence, when the
  proof-justified passes (O7, O8) may fire there (`Translate.RwState.site`). -/
  site : Option Name := none

/-- The kinds of image-kind auxiliaries (design document §4.5). -/
inductive AuxKind where
  | kRec | kRecOn | kCasesOn | kBelow | kBRecOn | kGo | kEq
  deriving BEq, Repr, Inhabited

def AuxKind.tag : AuxKind → String
  | .kRec => "rec" | .kRecOn => "recOn" | .kCasesOn => "casesOn" | .kBelow => "below"
  | .kBRecOn => "brecOn" | .kGo => "brecOn.go" | .kEq => "brecOn.eq"

/-- `s` is `kind` or `kind_j` (`j ≥ 1`): `some (some j)` or `some none`. -/
def suffixIdx? (kind s : String) : Option (Option Nat) :=
  if s == kind then some none
  else if s.startsWith (kind ++ "_") then
    match (s.drop (kind.length + 1)).toNat? with
    | some j => if j ≥ 1 then some (some j) else none
    | none => none
  else none

/-- The recursor `x.rec` or `x.rec_j` of a family root `x` and index. -/
def recNameOf (x : Name) : Option Nat → Name
  | none => Name.mkStr x "rec"
  | some j => Name.mkStr x s!"rec_{j}"

/-- Classify a Lean auxiliary name: its kind and the Lean recursor it is
built from (`x.casesOn ↦ (casesOn, x.rec)`, `all₀.brecOn_j.go ↦ (brecOn.go,
all₀.rec_j)`). Purely syntactic; the passes check the block's records. -/
def classify : Name → Option (AuxKind × Name)
  | .str p s _ =>
    if let some j := suffixIdx? "rec" s then some (.kRec, recNameOf p j)
    else if s == "recOn" then some (.kRecOn, recNameOf p none)
    else if s == "casesOn" then some (.kCasesOn, recNameOf p none)
    else if let some j := suffixIdx? "below" s then some (.kBelow, recNameOf p j)
    else if let some j := suffixIdx? "brecOn" s then some (.kBRecOn, recNameOf p j)
    else if s == "go" || s == "eq" then
      match p with
      | .str x t _ => match suffixIdx? "brecOn" t with
        | some j => some (if s == "go" then .kGo else .kEq, recNameOf x j)
        | none => none
      | _ => none
    else none
  | _ => none

/-- The Ix auxiliary of kind `k` next to the Ix recursor `ρ` (`P.rec ↦
P.casesOn`, `P.rec_k ↦ P.below_k`, …), by the reserved display names (D14).
`none` for a kind Lean does not have at a nested position (`casesOn`,
`recOn`). -/
def ixAuxOf (ρ : Name) (k : AuxKind) : Option Name :=
  match ρ with
  | .str p s _ => do
    let j ← suffixIdx? "rec" s
    let sfx := fun (base : String) => match j with
      | none => base
      | some j => s!"{base}_{j}"
    match k, j with
    | .kRec, _ => some ρ
    | .kRecOn, none => some (Name.mkStr p "recOn")
    | .kCasesOn, none => some (Name.mkStr p "casesOn")
    | .kRecOn, some _ | .kCasesOn, some _ => none
    | .kBelow, _ => some (Name.mkStr p (sfx "below"))
    | .kBRecOn, _ => some (Name.mkStr p (sfx "brecOn"))
    | .kGo, _ => some (Name.mkStr (Name.mkStr p (sfx "brecOn")) "go")
    | .kEq, _ => some (Name.mkStr (Name.mkStr p (sfx "brecOn")) "eq")
  | _ => none

/-- The shape of a generated image (see the module docstring). -/
structure RecShape where
  /-- The Lean recursor. -/
  leanRec : Name
  /-- Its universe parameters (the image's). -/
  levelParams : Array Name
  /-- Lean's telescope. -/
  np : Nat
  nm : Nat
  nmin : Nat
  ni : Nat
  /-- The Ix recursor the image applies. -/
  ixRec : Name
  /-- Its universe arguments, over `levelParams` (Def 3.4 step 2: `ℓ` first,
  `0` for a Prop member that gained large elimination). -/
  ixLevels : Array Level
  /-- Ix motive `k` is Lean motive `motiveSrc[k]`. -/
  motiveSrc : Array Nat
  /-- Ix minor `k` is Lean minor `j` (`some j`), or another term (`none`). -/
  minorSrc : Array (Option Nat)
  /-- The Ix minors as the image has them (under the image's λs). -/
  minorTerms : Array Expr
  deriving Inhabited

def RecShape.arity (s : RecShape) : Nat := s.np + s.nm + s.nmin + s.ni + 1

/-- Every Lean motive and minor is passed exactly once: the image is the Ix
recursor applied to a permutation of its arguments. -/
def RecShape.isPerm (s : RecShape) : Bool :=
  s.motiveSrc.size == s.nm && s.minorSrc.size == s.nmin
    && s.minorSrc.all Option.isSome
    && (List.range s.nm).all (fun i => s.motiveSrc.contains i)
    && (List.range s.nmin).all (fun j => s.minorSrc.contains (some j))

/-- Strip `n` leading λs. -/
def stripLams : Nat → Expr → Option Expr
  | 0, e => some e
  | n + 1, .lam _ _ b _ _ => stripLams n b
  | _, _ => none

/-- Read the shape off an image: `value` a λ over Lean's telescope (`np nm
nmin ni` and the major), `ixRecInfo ρ` the Ix recursor's counts. -/
def readShape (leanRec : Name) (levelParams : Array Name) (np nm nmin ni : Nat) (value : Expr)
    (ixRecInfo : Name → Option RecursorVal) : Option RecShape := do
  let arity := np + nm + nmin + ni + 1
  let body ← stripLams arity value
  let (h, args) := getAppFnArgs body
  let .const ρ ls _ := h | none
  let iv ← ixRecInfo ρ
  if iv.numParams != np || iv.numIndices != ni then none
  if args.size != np + iv.numMotives + iv.numMinors + ni + 1 then none
  -- the Lean telescope position of a bound variable of the body
  let pos? := fun (e : Expr) => match e with
    | .bvar k _ => if k < arity then some (arity - 1 - k) else none
    | _ => none
  -- parameters, indices and the major: the image's own, in order
  for i in [0:np] do
    if pos? args[i]! != some i then none
  for i in [0:ni + 1] do
    if pos? args[np + iv.numMotives + iv.numMinors + i]! != some (np + nm + nmin + i) then none
  let mut motiveSrc : Array Nat := #[]
  for k in [0:iv.numMotives] do
    let p ← pos? args[np + k]!
    if p < np || p ≥ np + nm || motiveSrc.contains (p - np) then none
    motiveSrc := motiveSrc.push (p - np)
  let mut minorSrc : Array (Option Nat) := #[]
  let mut minorTerms : Array Expr := #[]
  for k in [0:iv.numMinors] do
    let a := args[np + iv.numMotives + k]!
    minorTerms := minorTerms.push a
    match pos? a with
    | some p =>
      if p < np + nm || p ≥ np + nm + nmin || minorSrc.contains (some (p - np - nm)) then none
      minorSrc := minorSrc.push (some (p - np - nm))
    | none => minorSrc := minorSrc.push none
  return { leanRec, levelParams, np, nm, nmin, ni, ixRec := ρ, ixLevels := ls,
           motiveSrc, minorSrc, minorTerms }

/-- The data of one changed Lean block the passes read. -/
structure OptBlock where
  all : Array Name
  change : BlockChange
  /-- The canonical class of each member (Pass 1). -/
  classOf : Std.HashMap Name (Array Name)
  /-- The shapes of the block's Lean recursors (those that have one). -/
  shapes : Std.HashMap Name RecShape
  /-- The generated images of the block's Lean recursors (those that built):
  their universe parameters and values, read by the proof-justified passes
  over collapsed blocks, whose images are packed (`Opt.Packed`). -/
  images : Std.HashMap Name (Array Name × Expr) := {}
  /-- The Ix recursors of the block's canonical components (view names
  mapped back, as the images name them). -/
  ixRecs : Std.HashMap Name RecursorVal := {}
  deriving Inhabited

/-- What the passes read of the compiler. -/
structure OptEnv where
  /-- The input environment (Lean's auxiliaries and their types). -/
  ienv : Ix.Environment
  /-- A name of `E` resolves to an address. -/
  resolves : Name → Bool
  /-- The address of a name of `E`, when it resolves (the proof-justified
  passes compare compiled references, `Opt.CollapseRec.agreeAddr`). -/
  addrOf : Name → Option Address := fun _ => none
  /-- The block of a Lean image-kind head, when it is a changed block's. -/
  blockOf : Name → Option OptBlock
  /-- The dependents rule of the proof-justified passes (design document
  §1.4, order constraint 4, demotion): `demotion c key` names a dependent of
  the definition `c` (a constant outside `c`'s block that references `c`)
  which also references an image-kind auxiliary of the changed block `key`,
  i.e. may rely on `c` unfolding to its Lean shape; `none` when there is no
  such dependent. -/
  demotion : Name → Name → Option String := fun _ _ => none

/-- A constant of the input environment. -/
def OptEnv.const? (env : OptEnv) (n : Name) : Option ConstantInfo := env.ienv.get? n

/-- The universe arguments of the Ix auxiliary at an occurrence: the image's
`ℓs` with the occurrence's levels for Lean's parameters. -/
def RecShape.levelsAt (s : RecShape) (us : Array Level) : Array Level :=
  s.ixLevels.map (substLevel s.levelParams us)

/-- Arguments `src[k]` for `k` in order (Ix order from Lean order). -/
def pick (xs : Array Expr) (src : Array Nat) : Option (Array Expr) :=
  src.mapM (xs[·]?)

/-- The number of syntactic `∀` binders of a type. -/
def forallArity : Expr → Nat
  | .forallE _ _ b _ _ => forallArity b + 1
  | .mdata _ b _ => forallArity b
  | _ => 0

/-- Lean's auxiliary `a` has the standard telescope of its kind over the
recursor of `s` (`casesOn`: `ps motive is t minorsₓ`, with `nctors` minors),
and the same universe parameters as the recursor. -/
def standardTelescope (env : OptEnv) (s : RecShape) (k : AuxKind) (a : Name) (nctors : Nat := 0) :
    Option Nat := do
  let ci ← env.const? a
  if ci.getCnst.levelParams != s.levelParams then none
  let n := match k with
    | .kRec | .kRecOn => s.np + s.nm + s.nmin + s.ni + 1
    | .kCasesOn => s.np + 1 + s.ni + 1 + nctors
    | .kBelow => s.np + s.nm + s.ni + 1
    | .kBRecOn | .kGo | .kEq => s.np + s.nm + s.ni + 1 + s.nm
  if forallArity ci.getCnst.type != n then none
  return n

end Ix.Compile.Pass.Opt

end
