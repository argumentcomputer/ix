module

public import IxC.Kernel.Roles
public import Ix.SpecDigest

/-! # The role specifications, rendered for the circuit

IxVM reads a claim's primitives through its role binding and validates each
bound role against IxC's specification (`Ix.Kernel.Role.spec`) before using
it. The circuit cannot evaluate Lean data, so this module renders the
specification set as Aiur source: `Ix/IxVM/Kernel/RoleSpec.lean`, which
`lake exe ix codegen` writes and `lake exe ix codegen --check`
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
- the family of native rules that fires on the role's constant
  (`role_prim_family`), which is IxVM's, not the specification's.

The groups are validated in `groupOrder`: a group's roles are bound
together (`Role.block`), and every role a group needs (`Role.deps`) is in an
earlier group. The axioms come before the well-founded operations, whose
certificates use `propext`. The tail comes last: the well-founded operations'
groups, the groups of the definitions specified by their equations, and the
groups that need them. The circuit validates every tail group under the groups
before the tail (`first_well_founded_group`), so that no operation's or
definition's fast path takes part in validating another. -/

@[expose] public section

namespace IxVM.RoleSpecGen

open Ix.Kernel

/-- The groups, by their first role, in validation order. -/
def groupOrder : List Role :=
  [.nat, .eq, .punit, .empty, .false, .quot, .char, .string, .list, .charOfNat,
   .stringOfList, .bool, .natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq,
   .natBle, .true, .and, .iff, .nonempty, .propext, .choice, .sorryAx,
   .notProp, .decidable, .natLe, .int, .intLe, .bitVec, .byteArray,
   .natDiv, .natMod, .natGcd, .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight,
   .decidableDecide, .ofDecideEqTrue, .ofDecideEqFalse, .natDecEq, .natDecLe, .natDecLt,
   .intNegOfNat, .intSubNatNat, .intNeg, .intAdd, .intSub, .intMul, .intNatAbs, .intEdiv,
   .intEmod, .intPow, .bitVecToNat, .bitVecUlt, .stringDecEq, .stringToByteArray,
   .listAppend, .stringAppend, .ifThenElse, .intDecEq, .intDecLe, .intDecLt, .intBmod, .intBdiv,
   .charUtf8Size, .stringUtf8ByteSize, .stringBack]

def groups : List (List Role) := groupOrder.map Role.block

def roleIdx (r : Role) : Nat := Role.all.idxOf r

def groupOf (r : Role) : Nat := (groups.findIdx? (·.contains r)).getD groups.length

/-- The roles a group needs outside itself. -/
def groupNeeds (g : List Role) : List Role :=
  (g.flatMap Role.deps).eraseDups.filter (!g.contains ·)

/-- The group order covers every role once, each group is a block, and every
role a group needs is in an earlier group. -/
def checkGroups : Except String Unit := do
  let flat := groups.flatten
  unless flat.length == Role.all.length && Role.all.all flat.contains do
    throw "role groups do not cover every role exactly once"
  for (g, i) in groups.zipIdx do
    for r in g do
      unless Role.block r == g do throw s!"role group {i} is not {repr r}'s block"
    for r in groupNeeds g do
      unless groupOf r < i do throw s!"role group {i} needs {repr r}, which is not earlier"

/-- `natZero` ↦ `nat_zero`. -/
def snake (s : String) : String :=
  s.foldl (fun acc c => if c.isUpper then acc ++ "_" ++ (toString c.toLower) else acc.push c) ""

def roleName (r : Role) : String :=
  snake (((toString (repr r)).splitOn ".").getLast!)

/-! ## Terms -/

def list (xs : List String) : String :=
  xs.foldr (fun x acc => s!"store(ListNode.Cons({x}, {acc}))") "store(ListNode.Nil)"

/-- A level under the level parameters `ps`: IxC names a parameter by its id,
the circuit by its position in the constant's list (`Eq.rec.{u_1, u}` lists
`u_1` first). -/
def level (ps : List LevelParam) : Level → Except String String
  | .zero => pure "store(KLevelNode.Zero)"
  | .succ u => do pure s!"store(KLevelNode.Succ({← level ps u}))"
  | .max u v => do pure s!"store(KLevelNode.Max({← level ps u}, {← level ps v}))"
  | .imax u v => do pure s!"store(KLevelNode.IMax({← level ps u}, {← level ps v}))"
  | .param i =>
    if ps.contains i then pure s!"store(KLevelNode.Param({ps.idxOf i}))"
    else throw s!"level parameter {i} is not among {ps}"

def roleKey : Key .anon → Except String Nat
  | .role r => pure (roleIdx r)
  | _ => throw "a specification mentions a key that is not a role"

/-- A term at `depth` enclosing binders. The open variables `fvar i` are the
binders a caller closes over, outermost first, so `fvar i` is `BVar (depth - 1
- i)`. -/
def expr (ps : List LevelParam) (depth : Nat) : Expr .anon → Except String String
  | .bvar i => pure s!"store(KExprNode.BVar({i}))"
  | .fvar i _ =>
    if i < depth then pure s!"store(KExprNode.BVar({depth - 1 - i}))"
    else throw s!"open variable {i} outside its binder"
  | .sort u => do pure s!"store(KExprNode.Srt({← level ps u}))"
  | .const k us => do
    pure s!"store(KExprNode.Const(role_bound_addr(tbl, {← roleKey k}), {list (← us.mapM (level ps))}))"
  | .app f a => do pure s!"store(KExprNode.App({← expr ps depth f}, {← expr ps depth a}))"
  | .lam t b _ => do pure s!"store(KExprNode.Lam({← expr ps depth t}, {← expr ps (depth + 1) b}))"
  | .forallE t b _ => do
    pure s!"store(KExprNode.Forall({← expr ps depth t}, {← expr ps (depth + 1) b}))"
  | .letE t v b _ => do
    pure s!"store(KExprNode.Let({← expr ps depth t}, {← expr ps depth v}, {← expr ps (depth + 1) b}))"
  | .lit _ => throw "a literal in a specification"
  | .proj s i e => do
    pure s!"store(KExprNode.Proj(role_bound_addr(tbl, {← roleKey s}), {i}, {← expr ps depth e}))"

/-- `Nat`, through the binding. -/
def natT : String := s!"store(KExprNode.Const(role_bound_addr(tbl, {roleIdx .nat}), store(ListNode.Nil)))"

/-- `λ (x y : Nat), side`. -/
def closeEquationSide (side : Expr .anon) : Except String String := do
  pure s!"store(KExprNode.Lam({natT}, store(KExprNode.Lam({natT}, {← expr [] 2 side}))))"

/-- `Π (x y : Nat) (h₀ : hyp₀) …, @Eq.{1} Nat lhs rhs`. -/
def closeCertificate (hyps : List (Expr .anon)) (lhs rhs : Expr .anon) :
    Except String String := do
  let depth := 2 + hyps.length
  let eqHead := s!"store(KExprNode.Const(role_bound_addr(tbl, {roleIdx .eq}), \
    store(ListNode.Cons(store(KLevelNode.Succ(store(KLevelNode.Zero))), store(ListNode.Nil)))))"
  let eqn := s!"store(KExprNode.App(store(KExprNode.App(store(KExprNode.App({eqHead}, {natT})), \
    {← expr [] depth lhs})), {← expr [] depth rhs}))"
  let mut body := eqn
  for (h, i) in hyps.zipIdx.reverse do
    body := s!"store(KExprNode.Forall({← expr [] (2 + i) h}, {body}))"
  pure s!"store(KExprNode.Forall({natT}, store(KExprNode.Forall({natT}, {body}))))"

/-! ## Per-role data -/

/-- The block member of `r` and the block it is in. -/
def member (r : Role) : Except String (ConstantInfo .anon × List (ConstantInfo .anon)) := do
  let .block decls := r.spec (md := .anon) | throw s!"{repr r} is not a block member"
  let some d := decls.find? (·.toConstantVal.name == .role r)
    | throw s!"{repr r}'s block does not declare it"
  pure (d, decls)

/-- How IxVM sees a block member: 0 inductive, 1 constructor, 2 recursor,
3 axiom, 4–7 the quotient type, constructor, lift and induction principle. -/
def memberKind (r : Role) : Except String Nat := do
  match r with
  | .quot => pure 4
  | .quotMk => pure 5
  | .quotLift => pure 6
  | .quotInd => pure 7
  | _ =>
    match (← member r).1 with
    | .indInfo .. => pure 0
    | .ctorInfo .. => pure 1
    | .recInfo .. => pure 2
    | .axiomInfo .. => pure 3
    | _ => throw s!"{repr r}: unexpected block member"

/-- A constructor's inductive role, index, parameter and field counts: the
constructors after an inductive in its block are its own, in order. -/
def ctorOf (r : Role) : Except String (Nat × Nat × Nat × Nat) := do
  let (d, decls) ← member r
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
def ctorCount (r : Role) : Except String Nat := do
  let (_, decls) ← member r
  let mut count := 0
  let mut mine := false
  for decl in decls do
    match decl, decl.toConstantVal.name with
    | .indInfo .., .role i => mine := i == r
    | .ctorInfo .., _ => if mine then count := count + 1
    | _, _ => pure ()
  pure count

/-- 0 block member, 1 anchor, 2 operation, 3 standard axiom, 4 the inert
axiom `sorryAx` (tolerated as a declaration, never usable), 5 definition
specified by its equations. -/
def specKind (r : Role) : Nat :=
  match r.spec (md := .anon) with
  | .block _ => 0
  | .anchor .. => 1
  | .ops .. => 2
  | .axiom .. => if r == .sorryAx then 4 else 3
  | .eqns .. => 5

def levels (r : Role) : Except String Nat := do
  match r.spec (md := .anon) with
  | .block _ => pure (← member r).1.toConstantVal.levelParams.length
  | .anchor n _ => pure n
  | .ops .. => pure 0
  | .axiom n _ => pure n
  | .eqns n _ _ => pure n

/-- The specified type; an axiom of any type has none (`Sort 0` stands in). -/
def specType (r : Role) : Except String String := do
  match r.spec (md := .anon) with
  | .block _ =>
    let v := (← member r).1.toConstantVal
    expr v.levelParams 0 v.type
  | .anchor n t => expr (List.range n) 0 t
  | .ops t _ => expr [] 0 t
  | .axiom n (some t) => expr (List.range n) 0 t
  | .axiom _ none => pure "store(KExprNode.Srt(store(KLevelNode.Zero)))"
  | .eqns n t _ => expr (List.range n) 0 t

def equations (r : Role) : List (List (Expr .anon) × Expr .anon × Expr .anon) :=
  match r.spec (md := .anon) with
  | .ops _ eqs => eqs
  | _ => []

/-- A definition's equations (`Spec.eqns`). -/
def eqnsEquations (r : Role) : List (Equation .anon) :=
  match r.spec (md := .anon) with
  | .eqns _ _ eqs => eqs
  | _ => []

/-- A group of well-founded operations: its equations are certificates,
which carry hypotheses. -/
def wellFounded (g : List Role) : Bool :=
  g.any fun r => (equations r).any (!·.1.isEmpty)

/-- A group that must be validated in the tail: a well-founded operation's,
or a definition's specified by its equations, so that no operation's or
definition's fast path takes part in validating another. -/
def tailOnly (g : List Role) : Bool :=
  wellFounded g || g.any fun r => specKind r == 5

/-- The index of the first group of the tail. The tail comes last: the
circuit validates each of its groups under the groups before the tail, so
none comes before a group it could otherwise use. Every group that must be
in the tail is (`tailOnly`), and so is every group that needs a tail group;
no other group is. -/
def firstWellFoundedGroup : Except String Nat := do
  let some first := groups.findIdx? tailOnly
    | throw "no well-founded operation's group"
  for (g, i) in groups.zipIdx do
    let needsTail := (groupNeeds g).any fun r => first ≤ groupOf r
    unless (tailOnly g || needsTail) == decide (first ≤ i) do
      throw s!"role group {i}: the tail must be exactly the groups that need it"
  pure first

/-- An equation's levels: positional, as for its definition. -/
def eqnLevels (r : Role) : List LevelParam := List.range (levels r |>.toOption.getD 0)

/-- `λ vars, side`: an unconditional equation's side, closed over its
variables. -/
def closeEqnSide (r : Role) (e : Equation .anon) (side : Expr .anon) : Except String String := do
  let ps := eqnLevels r
  let mut body ← expr ps e.vars.length side
  for (t, i) in e.vars.zipIdx.reverse do
    body := s!"store(KExprNode.Lam({← expr ps i t}, {body}))"
  pure body

/-- `Π vars, Π hyps, @Eq.{level} carrier lhs rhs`: an equation's statement,
which a proof's type must meet. -/
def closeEqnStatement (r : Role) (e : Equation .anon) : Except String String := do
  let ps := eqnLevels r
  let n := e.vars.length
  let depth := n + e.hyps.length
  let eqHead := s!"store(KExprNode.Const(role_bound_addr(tbl, {roleIdx .eq}), \
    {list [← level ps e.level]}))"
  let mut body := s!"store(KExprNode.App(store(KExprNode.App(store(KExprNode.App({eqHead}, \
    {← expr ps depth e.carrier})), {← expr ps depth e.lhs})), {← expr ps depth e.rhs}))"
  for (h, j) in e.hyps.zipIdx.reverse do
    body := s!"store(KExprNode.Forall({← expr ps (n + j) h}, {body}))"
  for (t, i) in e.vars.zipIdx.reverse do
    body := s!"store(KExprNode.Forall({← expr ps i t}, {body}))"
  pure body

/-- The family of native rules that fires on a role's constant: 1 `Nat`
operations, 2 `String`, 3 `BitVec`, 5 decision procedures, 6 `Int`; 0 none. -/
def primFamily : Role → Nat
  | .natSucc | .natPred | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natPow
  | .natGcd | .natBeq | .natBle | .natLand | .natLor | .natXor | .natShiftLeft
  | .natShiftRight => 1
  | .stringOfList | .stringUtf8ByteSize | .stringAppend | .stringBack | .stringToByteArray
  | .stringDecEq => 2
  | .bitVecToNat | .bitVecUlt => 3
  | .natDecEq | .natDecLe | .natDecLt | .intDecEq | .intDecLe | .intDecLt => 5
  | .intAdd | .intSub | .intMul | .intNeg | .intNatAbs | .intEdiv | .intEmod | .intBmod | .intBdiv
  | .intPow => 6
  | _ => 0

/-! ## The file -/

def header : String := "module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

/-! # The role specifications, as circuit terms

GENERATED by `lake exe ix codegen` from IxC's specifications
(`Ix.Kernel.Role.spec`, `Role.block`, `Role.deps`) by
`Ix/IxVM/RoleSpecGen.lean`; do not edit. `lake exe ix codegen --check` fails
when it is stale. The validators that read it are in
`Ix/IxVM/Kernel/Roles.lean`. -/

public section

namespace IxVM

set_option maxRecDepth 16384 in
def roleSpec := ⟦
"

def footer : String := "⟧

end IxVM

end
"

/-- A `match` on `r` over every role, with a final arm. -/
def byRole (f : Role → Except String String) (fallback : String) : Except String String := do
  let mut arms := ""
  for r in Role.all do
    arms := arms ++ s!"      {roleIdx r} => {← f r},\n"
  pure s!"    match r \{\n{arms}      _ => {fallback},\n    }"

def aiurFn (sig body : String) : String := s!"  {sig} \{\n{body}\n  }\n\n"

def render : Except String String := do
  checkGroups
  let digest ← Ix.SpecDigest.specDigest
  let bytes := digest.hash.data.toList.map fun b => s!"0x{hexOfByte b}u8"
  let mut out := header
  out := out ++ s!"  -- specVersion {specVersion}, specification digest {digest}.\n"
  out := out ++ aiurFn "fn spec_version() -> G" s!"    {specVersion}"
  out := out ++ aiurFn "fn spec_digest() -> Addr" s!"    store([{", ".intercalate bytes}])"
  out := out ++ aiurFn "fn role_count() -> G" s!"    {Role.all.length}"
  out := out ++ aiurFn "fn group_count() -> G" s!"    {groups.length}"
  out := out ++ aiurFn "fn first_well_founded_group() -> G" s!"    {← firstWellFoundedGroup}"
  for r in Role.all do
    out := out ++ aiurFn s!"fn role_{roleName r}() -> G" s!"    {roleIdx r}"
  out := out ++ aiurFn "fn role_group(r: G) -> G" (← byRole (fun r => pure (toString (groupOf r))) "0")
  let mut groupArms := ""
  let mut needArms := ""
  for (g, i) in groups.zipIdx do
    groupArms := groupArms ++ s!"      {i} => {list (g.map (toString ∘ roleIdx))},\n"
    needArms := needArms ++ s!"      {i} => {list ((groupNeeds g).map (toString ∘ roleIdx))},\n"
  out := out ++ aiurFn "fn group_roles(g: G) -> List‹G›"
    s!"    match g \{\n{groupArms}      _ => store(ListNode.Nil),\n    }"
  out := out ++ aiurFn "fn group_needs(g: G) -> List‹G›"
    s!"    match g \{\n{needArms}      _ => store(ListNode.Nil),\n    }"
  out := out ++ aiurFn "fn role_spec_kind(r: G) -> G" (← byRole (fun r => pure (toString (specKind r))) "0")
  out := out ++ aiurFn "fn role_levels(r: G) -> G" (← byRole (fun r => do return toString (← levels r)) "0")
  out := out ++ aiurFn "fn role_member_kind(r: G) -> G"
    (← byRole (fun r => do
      if specKind r != 0 then return "0"
      return toString (← memberKind r)) "0")
  out := out ++ aiurFn "fn role_ctor_of(r: G) -> (G, G, G, G)"
    (← byRole (fun r => do
      if specKind r != 0 then return "(0, 0, 0, 0)"
      if (← memberKind r) != 1 then return "(0, 0, 0, 0)"
      let (i, c, p, f) ← ctorOf r
      pure s!"({i}, {c}, {p}, {f})") "(0, 0, 0, 0)")
  out := out ++ aiurFn "fn role_ctor_count(r: G) -> G"
    (← byRole (fun r => do
      if specKind r != 0 then return "0"
      if (← memberKind r) != 0 then return "0"
      return toString (← ctorCount r)) "0")
  out := out ++ aiurFn "fn role_type(tbl: RoleTable, r: G) -> KExpr"
    (← byRole specType "store(KExprNode.Srt(store(KLevelNode.Zero)))")
  out := out ++ aiurFn "fn op_equation_count(r: G) -> G"
    (← byRole (fun r => pure (toString (equations r).length)) "0")
  out := out ++ aiurFn "fn op_evidence_is_proof(r: G) -> G"
    (← byRole (fun r => pure (if (equations r).any (!·.1.isEmpty) then "1" else "0")) "0")
  -- Equation sides and certificates, by role and equation index.
  let mut lhsArms := ""
  let mut rhsArms := ""
  let mut certArms := ""
  for r in Role.all do
    for ((hyps, l, rhs), k) in (equations r).zipIdx do
      let key := 64 * roleIdx r + k
      if hyps.isEmpty then
        lhsArms := lhsArms ++ s!"      {key} => {← closeEquationSide l},\n"
        rhsArms := rhsArms ++ s!"      {key} => {← closeEquationSide rhs},\n"
      else
        certArms := certArms ++ s!"      {key} => {← closeCertificate hyps l rhs},\n"
  let dummy := "store(KExprNode.Srt(store(KLevelNode.Zero)))"
  out := out ++ aiurFn "fn op_equation_lhs(tbl: RoleTable, r: G, k: G) -> KExpr"
    s!"    match 64 * r + k \{\n{lhsArms}      _ => {dummy},\n    }"
  out := out ++ aiurFn "fn op_equation_rhs(tbl: RoleTable, r: G, k: G) -> KExpr"
    s!"    match 64 * r + k \{\n{rhsArms}      _ => {dummy},\n    }"
  out := out ++ aiurFn "fn op_certificate(tbl: RoleTable, r: G, k: G) -> KExpr"
    s!"    match 64 * r + k \{\n{certArms}      _ => {dummy},\n    }"
  -- Definitions specified by their equations, by role and equation index.
  out := out ++ aiurFn "fn eqns_equation_count(r: G) -> G"
    (← byRole (fun r => pure (toString (eqnsEquations r).length)) "0")
  let mut condArms := ""
  let mut eLhsArms := ""
  let mut eRhsArms := ""
  let mut stmtArms := ""
  for r in Role.all do
    for (e, k) in (eqnsEquations r).zipIdx do
      let key := 64 * roleIdx r + k
      stmtArms := stmtArms ++ s!"      {key} => {← closeEqnStatement r e},\n"
      if e.hyps.isEmpty then
        eLhsArms := eLhsArms ++ s!"      {key} => {← closeEqnSide r e e.lhs},\n"
        eRhsArms := eRhsArms ++ s!"      {key} => {← closeEqnSide r e e.rhs},\n"
      else
        condArms := condArms ++ s!"      {key} => 1,\n"
  out := out ++ aiurFn "fn eqns_conditional(r: G, k: G) -> G"
    s!"    match 64 * r + k \{\n{condArms}      _ => 0,\n    }"
  out := out ++ aiurFn "fn eqns_lhs(tbl: RoleTable, r: G, k: G) -> KExpr"
    s!"    match 64 * r + k \{\n{eLhsArms}      _ => {dummy},\n    }"
  out := out ++ aiurFn "fn eqns_rhs(tbl: RoleTable, r: G, k: G) -> KExpr"
    s!"    match 64 * r + k \{\n{eRhsArms}      _ => {dummy},\n    }"
  out := out ++ aiurFn "fn eqns_statement(tbl: RoleTable, r: G, k: G) -> KExpr"
    s!"    match 64 * r + k \{\n{stmtArms}      _ => {dummy},\n    }"
  out := out ++ aiurFn "fn role_prim_family(r: G) -> G"
    (← byRole (fun r => pure (toString (primFamily r))) "0")
  pure (out ++ footer)

end IxVM.RoleSpecGen

end
