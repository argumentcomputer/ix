module

public import IxC.Kernel.Roles
public import IxC.Kernel.RoleEquations
public import Ix.SpecDigest.Decode

/-! # The role specifications, rendered for the circuit

IxVM reads a claim's primitives through its role binding and validates each
bound role against IxC's specification (`Ix.Kernel.Role.spec`) before using
it. The circuit cannot evaluate Lean data, so this module renders the
specification set as Formal Aiur source, the Lean file
`IxVM/IxVM/Source/KernelRoleSpec.lean` (an `aiur⟦ … ⟧` block),
which `lake exe ix codegen` writes and `lake exe ix codegen --check`
compares against this renderer. The rendered file names `specVersion` and the
specification digest, so a change to the specifications that is not
regenerated here fails that check.

What is rendered, per role:

- its index in `Role.all` (`role_<name>`), its group and the group order;
- its specification kind and level-parameter count;
- for a block member, how IxVM sees it (inductive, constructor, recursor,
  axiom or one of the quotient kinds), and for a constructor its inductive,
  index, parameter and field counts;
- the specified type, with every role key read through the binding table;
- for an operation, its equations closed over `x y : Nat`, and for a
  well-founded one its certificate statements closed over `x y` and the
  hypotheses;
- for a definition specified by its equations, each unconditional equation's
  sides closed over its typed variables, and every equation's statement
  (`Π vars, Π hyps, Eq lhs rhs`), which a proof must meet;
- the native rule that fires on the role's constant (`role_prim_family`).

The renderer reads only the specification digest's bytes
(`Ix.SpecDigest.specBytes`), read back by `Ix.SpecDigest.Committed.ofBytes`
(`renderFromBytes`, "The source" below). The specifications give the kinds,
counts, types and equations. What the circuit reads off a role's identity
(its name, inertness, quotient kind and native rule: `Ix.SpecDigest.inert`,
`quotKind`, `nativeOp`) and the validation schedule (the group order and its
two boundaries, `Ix.SpecDigest.Schedule.current`,
`Ix/SpecDigest/Schedule.lean`) are defined beside the encoder, which commits to
them. So every value the rendered file holds comes from the bytes the digest
hashes, and `ix codegen --check` (`tools/ixvm/check-formal.sh`) fails when the
file and the digest drift apart. IxC's specification set and its schedule are
checked before rendering (`checkGroups`). -/

@[expose] public section

namespace IxVM.RoleSpecGen

open Ix.Kernel

export Ix.SpecDigest (groupOrder groups groupOf groupNeeds wellFounded tailOnly
  firstWellFoundedGroup firstEquationGroup)

def roleIdx (r : Role) : Nat := Role.all.idxOf r

/-- The role keys actually read by a closed generated term, including
projection heads and binder domains. Open variables and non-role keys do not
describe a closed role specification. -/
def referencedRoles : Expr .anon → Except String (List Role)
  | .bvar _ | .sort _ => pure []
  | .const (.role r) _ => pure [r]
  | .const _ _ => throw "a generated specification references a non-role key"
  | .proj (.role r) _ value => return r :: (← referencedRoles value)
  | .proj _ _ _ => throw "a generated specification projects a non-role key"
  | .app a b | .lam a b _ | .forallE a b _ =>
    return (← referencedRoles a) ++ (← referencedRoles b)
  | .letE type value body _ =>
    return (← referencedRoles type) ++ (← referencedRoles value) ++ (← referencedRoles body)
  | .fvar .. => throw "an open variable in a generated specification"
  | .lit _ => throw "a literal in a generated specification"

/-- The closed terms emitted for anchors and definitions specified by
equations. These use the equation checker's own telescope-closing functions. -/
def closedSpecTerms (r : Role) : List (Expr .anon) :=
  match r.spec (md := .anon) with
  | .anchor _ type => [type]
  | .eqns _ type equations =>
    type :: equations.flatMap fun equation =>
      equation.statement ::
        if equation.hyps.isEmpty then
          [equation.closedSide equation.lhs, equation.closedSide equation.rhs]
        else []
  | _ => []

/-- Every external generated reference is covered by a declared dependency
group. A group may refer to its own candidates, and naming any member of a
dependency group covers that whole group. -/
def checkReferenceGroups (g needs : List Role) (terms : List (Expr .anon)) :
    Except String Unit := do
  let allowed := g ++ needs.flatMap Role.block
  for term in terms do
    for role in ← referencedRoles term do
      unless allowed.contains role do
        throw s!"generated specification references {repr role} outside its declared dependency groups"


/-- The validation schedule is valid (`Ix.SpecDigest.Schedule.current`: it
covers every role once, each group is a block, every dependency group is
earlier, and both boundaries hold), and the dependency metadata covers the
actual generated anchor and equation references. -/
def checkGroups : Except String Unit := do
  let _ ← Ix.SpecDigest.Schedule.current
  for g in groups do
    checkReferenceGroups g (groupNeeds g) (g.flatMap closedSpecTerms)

/-- `natZero` ↦ `nat_zero`. -/
def snake (s : String) : String :=
  s.foldl (fun acc c => if c.isUpper then acc ++ "_" ++ (toString c.toLower) else acc.push c) ""

def roleName (r : Role) : String :=
  snake (((toString (repr r)).splitOn ".").getLast!)

/-! ## Terms -/

def list (xs : List String) : String :=
  xs.foldr (fun x acc => s!"(&(Lists::Node::Cons({x}, {acc})))") "(&(Lists::Node::Nil))"

/-- A structured pointer-valued circuit expression for per-arm DAG common
subexpression elimination. -/
inductive RVal where
  | raw (s : String)
  | node (pre : String) (args : List RVal) (suf : String)
  deriving BEq, Hashable, Inhabited

def rStore (ctor : String) (args : List RVal) : RVal :=
  if args.isEmpty then .node s!"(&({ctor}))" [] ""
  else .node s!"(&({ctor}(" args ")))"

def rBoundAddr (r : Nat) : RVal :=
  .node "KernelRoles::role_bound_addr(" [.raw "tbl", .raw (toString r)] ")"

def rNil : RVal := rStore "Lists::Node::Nil" []

def rList (xs : List RVal) : RVal :=
  xs.foldr (fun x acc => rStore "Lists::Node::Cons" [x, acc]) rNil

partial def collectPostOrder (v : RVal) (seen : Std.HashSet RVal) (order : Array RVal) :
    Std.HashSet RVal × Array RVal :=
  match v with
  | .raw _ => (seen, order)
  | .node _ args _ =>
    if seen.contains v then (seen, order)
    else
      let (seen, order) := args.foldl (fun (s, o) a => collectPostOrder a s o) (seen, order)
      (seen.insert v, order.push v)

/-- Render `root` as an Aiur match-arm body, hoisting any `.node` referenced
at least twice in the arm's DAG into a local `let x_i = ...;` binding. -/
def renderArm (root : RVal) : String := Id.run do
  let (_, order) := collectPostOrder root {} #[]
  let mut uses : Std.HashMap RVal Nat := ({} : Std.HashMap RVal Nat).insert root 1
  for n in order do
    if let .node _ args _ := n then
      for a in args do
        if let .node .. := a then
          uses := uses.insert a (uses.getD a 0 + 1)
  let mut env : Std.HashMap RVal String := {}
  let mut lets : String := ""
  let mut idx : Nat := 0
  for n in order do
    if let .node pre args suf := n then
      let renderedArgs := args.map fun a =>
        match a with
        | .raw s => s
        | _ => env.getD a ""
      let exprStr := s!"{pre}{", ".intercalate renderedArgs}{suf}"
      if uses.getD n 0 >= 2 && n != root then
        let varName := s!"x{idx}"
        idx := idx + 1
        lets := lets ++ s!"          let {varName} = {exprStr};\n"
        env := env.insert n varName
      else
        env := env.insert n exprStr
  let rootStr := match root with
    | .raw s => s
    | _ => env.getD root ""
  if lets.isEmpty then rootStr
  else s!"\n{lets}          {rootStr}"

/-- A level under the level parameters `ps`: IxC names a parameter by its id,
the circuit by its position in the constant's list (`Eq.rec.{u_1, u}` lists
`u_1` first). -/
def level (ps : List LevelParam) : Level → Except String RVal
  | .zero => pure (rStore "KernelTypes::KLevelNode::Zero" [])
  | .succ u => do pure (rStore "KernelTypes::KLevelNode::Succ" [← level ps u])
  | .max u v => do pure (rStore "KernelTypes::KLevelNode::Max" [← level ps u, ← level ps v])
  | .imax u v => do pure (rStore "KernelTypes::KLevelNode::IMax" [← level ps u, ← level ps v])
  | .param i =>
    if ps.contains i then pure (rStore "KernelTypes::KLevelNode::Param" [.raw (toString (ps.idxOf i))])
    else throw s!"level parameter {i} is not among {ps}"

def roleKey : Key .anon → Except String Nat
  | .role r => pure (roleIdx r)
  | _ => throw "a specification mentions a key that is not a role"

/-- A term at `depth` enclosing binders. The open variables `fvar i` are the
binders a caller closes over, outermost first, so `fvar i` is `BVar (depth - 1
- i)`. -/
def expr (ps : List LevelParam) (depth : Nat) : Expr .anon → Except String RVal
  | .bvar i => pure (rStore "KernelTypes::KExprNode::BVar" [.raw (toString i)])
  | .fvar i _ =>
    if i < depth then pure (rStore "KernelTypes::KExprNode::BVar" [.raw (toString (depth - 1 - i))])
    else throw s!"open variable {i} outside its binder"
  | .sort u => do pure (rStore "KernelTypes::KExprNode::Srt" [← level ps u])
  | .const k us => do
    pure (rStore "KernelTypes::KExprNode::Const" [rBoundAddr (← roleKey k), rList (← us.mapM (level ps))])
  | .app f a => do pure (rStore "KernelTypes::KExprNode::App" [← expr ps depth f, ← expr ps depth a])
  | .lam t b _ => do pure (rStore "KernelTypes::KExprNode::Lam" [← expr ps depth t, ← expr ps (depth + 1) b])
  | .forallE t b _ => do
    pure (rStore "KernelTypes::KExprNode::Forall" [← expr ps depth t, ← expr ps (depth + 1) b])
  | .letE t v b _ => do
    pure (rStore "KernelTypes::KExprNode::Let" [← expr ps depth t, ← expr ps depth v, ← expr ps (depth + 1) b])
  | .lit _ => throw "a literal in a specification"
  | .proj s i e => do
    pure (rStore "KernelTypes::KExprNode::Proj" [rBoundAddr (← roleKey s), .raw (toString i), ← expr ps depth e])

/-! ## The source: the specification digest's bytes

The renderer reads nothing but the bytes the specification digest is the
hash of (`Ix.SpecDigest.specBytes`), read back by
`Ix.SpecDigest.Committed.ofBytes`, which accepts them only when what it reads
re-encodes to them. A role is an index into those rows; `Role.all[i]` only
carries the index `i`. The circuit's own names for roles (`role_nat`, …) and
the roles its closing terms use (`Nat`, `Eq`) are looked up by the names the
bytes give. So every value the rendered file holds comes from the bytes, and
`ix codegen --check`, which compares the file with this rendering, fails when
the file and the digest drift apart. -/

/-- The decoded bytes and their digest. -/
structure Source where
  committed : Ix.SpecDigest.Committed
  digest : Address

/-- The source of `bytes`: refused unless they read back canonically
(`Ix.SpecDigest.Committed.ofBytes`) and give one row per role. -/
def Source.ofBytes (bytes : ByteArray) : Except String Source := do
  let committed ← Ix.SpecDigest.Committed.ofBytes bytes
  unless committed.rows.length == Role.all.length do
    throw s!"the specification bytes give {committed.rows.length} roles, not {Role.all.length}"
  return { committed, digest := Address.blake3Pure bytes }

/-- The row at `r`'s index. -/
def Source.row (src : Source) (r : Role) : Ix.SpecDigest.Row :=
  src.committed.rows.getD (roleIdx r) default

/-- The index of the role the bytes name `n`. -/
def Source.indexOf (src : Source) (n : Ix.Kernel.Name) : Except String Nat := do
  let parts ← Ix.SpecDigest.nameParts n
  match src.committed.rows.findIdx? (·.name == parts) with
  | some i => pure i
  | none => throw s!"the specification bytes name no role {n}"

/-- The roles a group needs outside itself, by the bytes' dependencies. -/
def Source.groupNeeds (src : Source) (g : List Role) : List Role :=
  (g.flatMap fun r => (src.row r).deps).eraseDups.filter (!g.contains ·)

/-- `Nat`, through the binding, at its index `nat`. -/
def natT (nat : Nat) : RVal := rStore "KernelTypes::KExprNode::Const" [rBoundAddr nat, rNil]

/-- `λ (x y : Nat), side`. -/
def closeEquationSide (nat : Nat) (side : Expr .anon) : Except String String := do
  let root := rStore "KernelTypes::KExprNode::Lam"
    [natT nat, rStore "KernelTypes::KExprNode::Lam" [natT nat, ← expr [] 2 side]]
  pure (renderArm root)

/-- `Π (x y : Nat) (h₀ : hyp₀) …, @Eq.{1} Nat lhs rhs`, for `Nat` and `Eq` at
the indices `nat` and `eq`. -/
def closeCertificate (nat eq : Nat) (hyps : List (Expr .anon)) (lhs rhs : Expr .anon) :
    Except String String := do
  let depth := 2 + hyps.length
  let eqHead := rStore "KernelTypes::KExprNode::Const"
    [rBoundAddr eq, rList [rStore "KernelTypes::KLevelNode::Succ" [rStore "KernelTypes::KLevelNode::Zero" []]]]
  let eqn := rStore "KernelTypes::KExprNode::App"
    [rStore "KernelTypes::KExprNode::App" [rStore "KernelTypes::KExprNode::App" [eqHead, natT nat], ← expr [] depth lhs],
     ← expr [] depth rhs]
  let mut body := eqn
  for (h, i) in hyps.zipIdx.reverse do
    body := rStore "KernelTypes::KExprNode::Forall" [← expr [] (2 + i) h, body]
  let root := rStore "KernelTypes::KExprNode::Forall"
    [natT nat, rStore "KernelTypes::KExprNode::Forall" [natT nat, body]]
  pure (renderArm root)

/-! ## Per-role data, from the source -/

/-- The block member of `r` and the block it is in. -/
def member (src : Source) (r : Role) :
    Except String (ConstantInfo .anon × List (ConstantInfo .anon)) := do
  let .block decls := (src.row r).spec | throw s!"{repr r} is not a block member"
  let some d := decls.find? (·.toConstantVal.name == .role r)
    | throw s!"{repr r}'s block does not declare it"
  pure (d, decls)

/-- How IxVM sees a block member: 0 inductive, 1 constructor, 2 recursor,
3 axiom, 4–7 the quotient type, constructor, lift and induction principle
(the row's quotient kind, 1–4). -/
def memberKind (src : Source) (r : Role) : Except String Nat := do
  let quot := (src.row r).quotKind
  if quot != 0 then return 3 + quot
  match (← member src r).1 with
  | .indInfo .. => pure 0
  | .ctorInfo .. => pure 1
  | .recInfo .. => pure 2
  | .axiomInfo .. => pure 3
  | _ => throw s!"{repr r}: unexpected block member"

/-- A constructor's inductive role, index, parameter and field counts: the
constructors after an inductive in its block are its own, in order. -/
def ctorOf (src : Source) (r : Role) : Except String (Nat × Nat × Nat × Nat) := do
  let (d, decls) ← member src r
  let .ctorInfo _ nP nF := d | throw s!"{repr r} is not a constructor"
  let mut ind? : Option Role := none
  let mut cidx := 0
  for decl in decls do
    match decl, decl.toConstantVal.name with
    | .indInfo .., .role i => ind? := some i; cidx := 0
    | .ctorInfo .., .role c =>
      if c == r then
        let some i := ind? | throw s!"{repr r} precedes its inductive"
        return (roleIdx i, cidx, nP, nF)
      cidx := cidx + 1
    | _, _ => pure ()
  throw s!"{repr r} not found in its block"

/-- An inductive's constructor count. -/
def ctorCount (src : Source) (r : Role) : Except String Nat := do
  let (_, decls) ← member src r
  let mut count := 0
  let mut mine := false
  for decl in decls do
    match decl, decl.toConstantVal.name with
    | .indInfo .., .role i => mine := i == r
    | .ctorInfo .., _ => if mine then count := count + 1
    | _, _ => pure ()
  pure count

/-- 0 block member, 1 anchor, 2 operation, 3 standard axiom, 4 the inert
axiom `sorryAx` (the row's `inert`: tolerated as a declaration, never
usable), 5 definition specified by its equations. -/
def specKind (src : Source) (r : Role) : Nat :=
  match (src.row r).spec with
  | .block _ => 0
  | .anchor .. => 1
  | .ops .. => 2
  | .axiom .. => if (src.row r).inert then 4 else 3
  | .eqns .. => 5

def levels (src : Source) (r : Role) : Except String Nat := do
  match (src.row r).spec with
  | .block _ => pure (← member src r).1.toConstantVal.levelParams.length
  | .anchor n _ => pure n
  | .ops .. => pure 0
  | .axiom n _ => pure n
  | .eqns n _ _ => pure n

/-- The specified type; an axiom of any type has none (`Sort 0` stands in). -/
def specType (src : Source) (r : Role) : Except String String := do
  match (src.row r).spec with
  | .block _ =>
    let v := (← member src r).1.toConstantVal
    pure (renderArm (← expr v.levelParams 0 v.type))
  | .anchor n t => pure (renderArm (← expr (List.range n) 0 t))
  | .ops t _ => pure (renderArm (← expr [] 0 t))
  | .axiom n (some t) => pure (renderArm (← expr (List.range n) 0 t))
  | .axiom _ none => pure "(&(KernelTypes::KExprNode::Srt((&(KernelTypes::KLevelNode::Zero)))))"
  | .eqns n t _ => pure (renderArm (← expr (List.range n) 0 t))

/-- An operation's equations (`Spec.ops`), from IxC's specification set. -/
def equations (r : Role) : List (List (Expr .anon) × Expr .anon × Expr .anon) :=
  match r.spec (md := .anon) with
  | .ops _ eqs => eqs
  | _ => []

/-- An operation's equations (`Spec.ops`), from the source. -/
def opEquations (src : Source) (r : Role) : List (List (Expr .anon) × Expr .anon × Expr .anon) :=
  match (src.row r).spec with
  | .ops _ eqs => eqs
  | _ => []

/-- A definition's equations (`Spec.eqns`), from the source. -/
def eqnsEquations (src : Source) (r : Role) : List (Equation .anon) :=
  match (src.row r).spec with
  | .eqns _ _ eqs => eqs
  | _ => []

/-- An equation's levels: positional, as for its definition. -/
def eqnLevels (src : Source) (r : Role) : List LevelParam :=
  List.range (levels src r |>.toOption.getD 0)

/-- `λ vars, side`: an unconditional equation's side, closed over its
variables. -/
def closeEqnSide (src : Source) (r : Role) (e : Equation .anon) (side : Expr .anon) :
    Except String String := do
  let ps := eqnLevels src r
  let mut body ← expr ps e.vars.length side
  for (t, i) in e.vars.zipIdx.reverse do
    body := rStore "KernelTypes::KExprNode::Lam" [← expr ps i t, body]
  pure (renderArm body)

/-- `Π vars, Π hyps, @Eq.{level} carrier lhs rhs`: an equation's statement,
which a proof's type must meet, for `Eq` at the index `eq`. -/
def closeEqnStatement (src : Source) (eq : Nat) (r : Role) (e : Equation .anon) :
    Except String String := do
  let ps := eqnLevels src r
  let n := e.vars.length
  let depth := n + e.hyps.length
  let eqHead := rStore "KernelTypes::KExprNode::Const" [rBoundAddr eq, rList [← level ps e.level]]
  let mut body := rStore "KernelTypes::KExprNode::App"
    [rStore "KernelTypes::KExprNode::App"
      [rStore "KernelTypes::KExprNode::App" [eqHead, ← expr ps depth e.carrier],
       ← expr ps depth e.lhs],
     ← expr ps depth e.rhs]
  for (h, j) in e.hyps.zipIdx.reverse do
    body := rStore "KernelTypes::KExprNode::Forall" [← expr ps (n + j) h, body]
  for (t, i) in e.vars.zipIdx.reverse do
    body := rStore "KernelTypes::KExprNode::Forall" [← expr ps i t, body]
  pure (renderArm body)

/-- The native rule that fires on a role's constant (the row's
`Ix.SpecDigest.nativeOp`): its family (1 `Nat` operations, 2 `String`,
3 `BitVec`, 5 decision procedures, 6 `Int`; 0 none) and the operation's index
within that family. -/
def primFamilyOp (src : Source) (r : Role) : Nat × Nat := (src.row r).native

/-! ## The file (`IxVM/IxVM/Source/KernelRoleSpec.lean`) -/

/-- The roles directly named by circuit modules (`role_<name>`). Each name's
index is the one the specification bytes give the role's Lean name. -/
def namedRoles : List Role :=
  [.nat, .natZero, .natSucc, .bool, .boolFalse, .boolTrue, .eq, .eqRefl,
   .listNil, .listCons, .quot, .quotMk, .quotLift, .quotInd, .quotSound,
   .string, .stringOfList, .char, .charOfNat, .natAdd, .propext, .choice,
   .sorryAx, .decidableIsTrue, .decidableIsFalse, .ofDecideEqTrue, .ofDecideEqFalse,
   .natLe, .natDecLe, .int, .intOfNat, .intNegSucc, .bitVecOfNat, .byteArrayEmpty,
   .intLe, .intDecLe]

def arm (k rhs : String) : String :=
  let sep := if rhs.startsWith "\n" then "" else "  "
  s!"        {k} => \{{sep}{rhs} } ,\n"

/-- A `match` on `r` over every role whose value differs from `fallback`, with
`fallback` as the final arm. -/
def byRole (f : Role → Except String String) (fallback : String) : Except String String := do
  let mut arms := ""
  for r in Role.all do
    let rhs ← f r
    if rhs != fallback then
      arms := arms ++ arm (toString (roleIdx r)) rhs
  pure s!"      match r \{\n{arms}{arm "_" fallback}      }"

def formalAiurFn (sig body : String) : String :=
  let name := (((sig.splitOn "fn ").getLast!).splitOn "(").head!
  s!"def {name} := aiur_fn⟦\n" ++
    s!"  {sig} \{\n{body}\n    }\n⟧"

/-- The rendered Lean file, up to its named function definitions. -/
def leanHeader : String := "import Aiur.Modules.Function

/-! # IxVM module `KernelRoleSpec`

Rendered from IxC's role specifications (`Ix.Kernel.Role.spec`) by
`IxVM.RoleSpecGen.renderFormalAiur`; do not edit. `lake exe ix codegen` writes
this file, and `lake exe ix codegen --check` fails when it is stale.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

-- Compiling the long role matches recurses past the default depth.
set_option maxRecDepth 32768
aiur_module KernelRoleSpec where

"

/-- Render the named functions and their module from the source alone. -/
def renderSource (src : Source) : Except String String := do
  let c := src.committed
  let schedule := c.schedule
  -- Equations are keyed `64 * role + index`.
  for r in Role.all do
    unless (opEquations src r).length < 64 && (eqnsEquations src r).length < 64 do
      throw s!"{repr r} has 64 or more equations, which the rendered keys cannot index"
  let nat ← src.indexOf Role.nat.leanName
  let eq ← src.indexOf Role.eq.leanName
  let bytes := src.digest.hash.data.toList.map fun b => s!"UInt8::BYTE_{b.toNat}"
  let mut fns : Array String := #[]
  fns := fns.push (formalAiurFn "inline fn spec_version() -> Field" s!"      {c.specVersion}")
  fns := fns.push (formalAiurFn "inline fn spec_digest() -> Bytes::AddressRef" s!"      (&([{", ".intercalate bytes}]))")
  fns := fns.push (formalAiurFn "inline fn role_count() -> Field" s!"      {c.rows.length}")
  fns := fns.push (formalAiurFn "inline fn group_count() -> Field" s!"      {schedule.groups.length}")
  fns := fns.push (formalAiurFn "inline fn first_well_founded_group() -> Field"
    s!"      {schedule.firstWellFounded}")
  fns := fns.push (formalAiurFn "inline fn first_equation_group() -> Field"
    s!"      {schedule.firstEquation}")
  for r in namedRoles do
    let index ← src.indexOf r.leanName
    fns := fns.push (formalAiurFn s!"inline fn role_{roleName r}() -> Field" s!"      {index}")
  fns := fns.push (formalAiurFn "fn role_group(r: Field) -> Field"
    (← byRole (fun r => pure (toString (groupOf r schedule.groups))) "0"))
  let mut groupArms := ""
  let mut needArms := ""
  for (g, i) in schedule.groups.zipIdx do
    groupArms := groupArms ++ arm (toString i) (list (g.map (toString ∘ roleIdx)))
    let needs := src.groupNeeds g
    unless needs.isEmpty do
      needArms := needArms ++ arm (toString i) (list (needs.map (toString ∘ roleIdx)))
  fns := fns.push (formalAiurFn "fn group_roles(g: Field) -> Lists::List<Field>"
    s!"      match g \{\n{groupArms}{arm "_" "(&(Lists::Node::Nil))"}      }")
  fns := fns.push (formalAiurFn "fn group_needs(g: Field) -> Lists::List<Field>"
    s!"      match g \{\n{needArms}{arm "_" "(&(Lists::Node::Nil))"}      }")
  fns := fns.push (formalAiurFn "fn role_spec_kind(r: Field) -> Field"
    (← byRole (fun r => pure (toString (specKind src r))) "0"))
  fns := fns.push (formalAiurFn "fn role_levels(r: Field) -> Field"
    (← byRole (fun r => do return toString (← levels src r)) "0"))
  fns := fns.push (formalAiurFn "fn role_member_kind(r: Field) -> Field"
    (← byRole (fun r => do
      if specKind src r != 0 then return "0"
      return toString (← memberKind src r)) "0"))
  fns := fns.push (formalAiurFn "fn role_ctor_of(r: Field) -> (Field, Field, Field, Field)"
    (← byRole (fun r => do
      if specKind src r != 0 then return "(0, 0, 0, 0)"
      if (← memberKind src r) != 1 then return "(0, 0, 0, 0)"
      let (i, c, p, f) ← ctorOf src r
      pure s!"({i}, {c}, {p}, {f})") "(0, 0, 0, 0)"))
  fns := fns.push (formalAiurFn "fn role_ctor_count(r: Field) -> Field"
    (← byRole (fun r => do
      if specKind src r != 0 then return "0"
      if (← memberKind src r) != 0 then return "0"
      return toString (← ctorCount src r)) "0"))
  let dummy := "(&(KernelTypes::KExprNode::Srt((&(KernelTypes::KLevelNode::Zero)))))"
  fns := fns.push (formalAiurFn "fn role_type(tbl: KernelRoles::RoleTable, r: Field) -> KernelTypes::KExpr"
    (← byRole (specType src) dummy))
  fns := fns.push (formalAiurFn "fn op_equation_count(r: Field) -> Field"
    (← byRole (fun r => pure (toString (opEquations src r).length)) "0"))
  fns := fns.push (formalAiurFn "fn op_evidence_is_proof(r: Field) -> Field"
    (← byRole (fun r => pure (if (opEquations src r).any (!·.1.isEmpty) then "1" else "0")) "0"))
  -- Equation sides and certificates, by role and equation index.
  let mut lhsArms := ""
  let mut rhsArms := ""
  let mut certArms := ""
  for r in Role.all do
    for ((hyps, l, rhs), k) in (opEquations src r).zipIdx do
      let key := toString (64 * roleIdx r + k)
      if hyps.isEmpty then
        lhsArms := lhsArms ++ arm key (← closeEquationSide nat l)
        rhsArms := rhsArms ++ arm key (← closeEquationSide nat rhs)
      else
        certArms := certArms ++ arm key (← closeCertificate nat eq hyps l rhs)
  fns := fns.push (formalAiurFn "fn op_equation_lhs(tbl: KernelRoles::RoleTable, r: Field, k: Field) -> KernelTypes::KExpr"
    s!"      match 64 * r + k \{\n{lhsArms}{arm "_" dummy}      }")
  fns := fns.push (formalAiurFn "fn op_equation_rhs(tbl: KernelRoles::RoleTable, r: Field, k: Field) -> KernelTypes::KExpr"
    s!"      match 64 * r + k \{\n{rhsArms}{arm "_" dummy}      }")
  fns := fns.push (formalAiurFn "fn op_certificate(tbl: KernelRoles::RoleTable, r: Field, k: Field) -> KernelTypes::KExpr"
    s!"      match 64 * r + k \{\n{certArms}{arm "_" dummy}      }")
  -- Definitions specified by their equations, by role and equation index.
  fns := fns.push (formalAiurFn "fn eqns_equation_count(r: Field) -> Field"
    (← byRole (fun r => pure (toString (eqnsEquations src r).length)) "0"))
  let mut condArms := ""
  let mut eLhsArms := ""
  let mut eRhsArms := ""
  let mut stmtArms := ""
  for r in Role.all do
    for (e, k) in (eqnsEquations src r).zipIdx do
      let key := toString (64 * roleIdx r + k)
      stmtArms := stmtArms ++ arm key (← closeEqnStatement src eq r e)
      if e.hyps.isEmpty then
        eLhsArms := eLhsArms ++ arm key (← closeEqnSide src r e e.lhs)
        eRhsArms := eRhsArms ++ arm key (← closeEqnSide src r e e.rhs)
      else
        condArms := condArms ++ arm key "1"
  fns := fns.push (formalAiurFn "fn eqns_conditional(r: Field, k: Field) -> Field"
    s!"      match 64 * r + k \{\n{condArms}{arm "_" "0"}      }")
  fns := fns.push (formalAiurFn "fn eqns_lhs(tbl: KernelRoles::RoleTable, r: Field, k: Field) -> KernelTypes::KExpr"
    s!"      match 64 * r + k \{\n{eLhsArms}{arm "_" dummy}      }")
  fns := fns.push (formalAiurFn "fn eqns_rhs(tbl: KernelRoles::RoleTable, r: Field, k: Field) -> KernelTypes::KExpr"
    s!"      match 64 * r + k \{\n{eRhsArms}{arm "_" dummy}      }")
  fns := fns.push (formalAiurFn "fn eqns_statement(tbl: KernelRoles::RoleTable, r: Field, k: Field) -> KernelTypes::KExpr"
    s!"      match 64 * r + k \{\n{stmtArms}{arm "_" dummy}      }")
  fns := fns.push (formalAiurFn "fn role_prim_family(r: Field) -> (Field, Field)"
    (← byRole (fun r => do
      let (fam, op) := primFamilyOp src r
      pure s!"({fam}, {op})") "(0, 0)"))
  pure (leanHeader ++ "\n\n".intercalate fns.toList ++
    "\n\nend\n\nend IxVM\n")

/-- **`KernelRoleSpec.lean`, rebuilt from the specification bytes alone.** -/
def renderFromBytes (bytes : ByteArray) : Except String String := do
  renderSource (← Source.ofBytes bytes)

/-- The first line where `a` and `b` differ, for a check's message. -/
def firstDifference (a b : String) : String := Id.run do
  let xs := a.splitOn "\n"
  let ys := b.splitOn "\n"
  let clip (s : String) : String := String.ofList (s.toList.take 80)
  for i in [0:max xs.length ys.length] do
    let x := xs.getD i "<end of file>"
    let y := ys.getD i "<end of file>"
    if x != y then
      return s!"line {i + 1}: expected {clip x}, found {clip y}"
  return "no line differs"

/-- **The rendering check**: `file` is `KernelRoleSpec.lean` rebuilt from the
specification bytes `bytes`, or the check fails with the first difference. -/
def checkRendering (bytes : ByteArray) (file : String) : Except String Unit := do
  let rendered ← renderFromBytes bytes
  unless rendered == file do
    throw s!"KernelRoleSpec.lean is not the rendering of the specification bytes \
      (digest {Address.blake3Pure bytes}): {firstDifference rendered file}"

/-- Render `IxVM/IxVM/Source/KernelRoleSpec.lean` from the specification
digest's bytes, once IxC's specification set and its schedule are checked
(`checkGroups`). `ix codegen` writes it and `ix codegen --check` compares. -/
def renderFormalAiur : Except String String := do
  checkGroups
  renderFromBytes (← Ix.SpecDigest.specBytes)

/-- An independent wire-shape fixture for Rust's candidate checks. -/
def renderSpecShapeTsv : String := Id.run do
  let indices (roles : List Role) :=
    ",".intercalate (roles.map fun r => toString (roleIdx r))
  let kind : Option Bool → String
    | some true => "defeq"
    | some false => "proof"
    | none => "either"
  let mut out := s!"# Role.block/deps and Spec.evidenceAllowed, version{specVersion}\n"
  for r in Role.all do
    let kinds := ",".intercalate ((r.spec (md := .anon)).evidenceAllowed.map kind)
    out := out ++ s!"{roleIdx r}\t{indices r.block}\t{indices r.deps}\t{kinds}\n"
  return out

end IxVM.RoleSpecGen

end
