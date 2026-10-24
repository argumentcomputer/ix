/-
  The shared helpers of the clique library's suites (`clique-recognition`,
  `clique-transport`; the library is `Ix.Compile.Pass.Clique`, unwired, so
  these suites are its only coverage):

  * the fixtures' environment (the twin families and
    `Tests.Ix.Compile.Clique.Fixtures`, loaded at run time with the twins:
    `Tests.Ix.Compile.Twins.fixturesEnv`) and the conversions between Lean
    and Ix terms; the library's input constants as a lookup and as an
    `Ix.Environment` (lazy, with an optional overlay of replaced or added
    constants, for the adversarial inputs);
  * `eqUpTo`, the tests' comparison up to binder names, `mdata` and a name
    map (the library compares with `alphaEqSkipMdata` and keeps no name map);
  * the kernel (`kernelAdd`, synchronous);
  * the measure mask of the GuessLex policy (`maskMeasures`);
  * the recovered specifications of a clique and the order they give
    (`recoverSpecs`, `recoveredOrder`), which the library leaves to its tests
    (its own order is `cliqueOrder`, over the normalised specifications).
-/
import Ix.Meta
import Ix.CanonM
import Ix.Compile.Canon
import Ix.Compile.Pass.Clique
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.SourceFamilyOracle

open Lean

namespace Tests.Ix.Compile.Clique.Common

open _root_.Ix.Compile.Pass.Clique (Decl Input)

abbrev IxName := _root_.Ix.Name
abbrev IxExpr := _root_.Ix.Expr
abbrev IxConst := _root_.Ix.ConstantInfo

/-! ## Names, terms and constants -/

def ixName (n : Name) : IxName := _root_.Ix.Name.fromLeanName n

def toLeanName : IxName → Name
  | .anonymous _ => .anonymous
  | .str p s _ => .str (toLeanName p) s
  | .num p n _ => .num (toLeanName p) n

def toIxConst (c : ConstantInfo) : IxConst := (_root_.Ix.CanonM.canonConst c).run' {}
def toIxExpr (e : Expr) : IxExpr := (_root_.Ix.CanonM.canonExpr e).run' {}
def toLeanExpr (e : IxExpr) : Expr := (_root_.Ix.CanonM.uncanonExpr e).run' {}

/-- A definition or theorem of `env` as the library's declaration. -/
def declOf (env : Environment) (n : Name) : Option Decl :=
  (env.find? n).bind fun ci => Decl.ofConstantInfo? (toIxConst ci)

/-- The library's input constants: `env`'s, converted on lookup. -/
def constOf (env : Environment) (n : IxName) : Option IxConst :=
  (env.find? (toLeanName n)).map toIxConst

/-- The library's input as an `Ix.Environment`: the constants of `overlay`
first (replaced or added constants), then `env`'s, converted on lookup. -/
def ixEnvOf (env : Environment) (overlay : Std.HashMap IxName IxConst := {}) :
    _root_.Ix.Environment :=
  { consts := overlay, fallback? := some (constOf env) }

/-- A declaration as an input constant (a theorem, or a safe definition),
for an overlay. -/
def constOfDecl (d : Decl) : IxConst :=
  let cnst : _root_.Ix.ConstantVal := { name := d.name, levelParams := d.levelParams, type := d.type }
  if d.isThm then .thmInfo { cnst, value := d.value, all := #[d.name] }
  else .defnInfo { cnst, value := d.value, hints := .opaque, safety := .safe, all := #[d.name] }

/-- The root module of the clique fixtures, and a name under it. -/
def fixturesRoot : Name := `Tests.Ix.Compile.Clique.Fixtures
def fx (s : String) : Name := fixturesRoot ++ s.toName

/-- The environment of the twin families and the clique fixtures. -/
def fixturesEnv : IO Environment := Tests.Ix.Compile.Twins.fixturesEnv

/-- The private name whose user name is `user` (the module part of a
private name depends on the module that declares it). -/
def privateNamed? (env : Environment) (user : Name) : Option Name :=
  env.constants.fold (init := none) fun acc n _ =>
    if acc.isNone && Lean.privateToUserName? n == some user then some n else acc

/-! ## Comparison -/

/-- Equality up to binder names, binder info and `mdata`, with the constant
names of `b` mapped by `mapB` (the donor library's test comparison; the
library itself compares with `alphaEqSkipMdata`, without a name map). -/
def eqUpTo (mapB : IxName → IxName) : IxExpr → IxExpr → Bool
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

/-- Mask the measures: `invImage`'s function and `WellFounded.Nat.fix`'s
measure become a placeholder (GuessLex's choice lives there). `partial`, as
in the donor: the walk recurses through `getAppFnArgs`' argument array. -/
partial def maskMeasures (e : IxExpr) : IxExpr :=
  match e with
  | .app .. =>
    let (h, args) := _root_.Ix.Compile.Canon.getAppFnArgs e
    let args := args.map maskMeasures
    let placeholder := _root_.Ix.Expr.mkConst (ixName `_measure) #[]
    let args := match h with
      | .const c _ _ =>
        if (c == ixName ``invImage || c == ixName ``WellFounded.Nat.fix) && args.size ≥ 3 then
          args.set! 2 placeholder
        else if c == ixName ``InvImage && args.size ≥ 4 then args.set! 3 placeholder
        else args
      | _ => args
    _root_.Ix.Compile.Canon.mkAppN (maskMeasures h) args
  | .lam n t b bi _ => _root_.Ix.Expr.mkLam n (maskMeasures t) (maskMeasures b) bi
  | .forallE n t b bi _ => _root_.Ix.Expr.mkForallE n (maskMeasures t) (maskMeasures b) bi
  | .letE n t v b nd _ =>
    _root_.Ix.Expr.mkLetE n (maskMeasures t) (maskMeasures v) (maskMeasures b) nd
  | .proj s i x _ => _root_.Ix.Expr.mkProj s i (maskMeasures x)
  | .mdata d x _ => _root_.Ix.Expr.mkMData d (maskMeasures x)
  | e => e

/-! ## The kernel -/

/-- Add `decl` with Lean's kernel, synchronously (`Elab.async false`, so a
rejection is reported here); the error message, or `none`. -/
def kernelAdd (decl : Declaration) : CoreM (Option String) := do
  try
    withOptions (fun o => o.setBool `Elab.async false) do addDecl decl
    return none
  catch e =>
    return some (← e.toMessageData.toString)

/-- `kernelAdd`, failing on a rejection. -/
def kernelAddOrThrow (decl : Declaration) : CoreM Unit := do
  if let some why ← kernelAdd decl then
    throwError "kernel rejected {decl.getNames}: {why}"

/-- A library declaration as a kernel declaration, its names mapped by
`rename` (its own name included). -/
def kernelOfDecl (d : Decl) (rename : IxName → Option IxName := fun _ => none) : Declaration :=
  let name := toLeanName ((rename d.name).getD d.name)
  let levelParams := d.levelParams.toList.map toLeanName
  let type := toLeanExpr (_root_.Ix.Compile.Pass.Clique.renameConsts rename d.type)
  let value := toLeanExpr (_root_.Ix.Compile.Pass.Clique.renameConsts rename d.value)
  if d.isThm then .thmDecl { name, levelParams, type, value }
  else .defnDecl { name, levelParams, type, value, hints := .opaque, safety := .safe }

/-! ## The recovered order (the library's tests only)

The donor library had `recoverSpecs`/`recoveredOrder` (test-only); the port
left them out. They are rebuilt here from the library's pieces. -/

open _root_.Ix.Compile.Pass.Clique in
/-- The recovered specifications of a clique (`inp.members` in Lean's order;
`inp.sigma` is ignored): each member's body with its recursion made explicit
again, checked by re-encoding. A structural clique needs the authenticated
family (`inp.family`). -/
def recoverSpecs (inp : Input) : Except String (Array IxExpr) :=
  let r : TM (Array IxExpr) := match inp.encoding with
    | .structural => recoverStructural inp.members inp.aux inp.const? inp.family
    | .wellFounded => do
      let some packed := findPacked? inp.members inp.aux
        | throw "recovery: no packed function"
      recoverWF inp.members packed inp.const?
    | .partialFixpoint => throw "recovery: a theorem clique has no partial_fixpoint route"
  r.run'

open _root_.Ix.Compile.Pass.Clique in
/-- The canonical order of a theorem clique by its statements and, among tied
statements, its recovered specifications (Pass 1's classes over statement and
recovered body, the compiler's rules). `σ[i]` is the canonical position of
Lean's member `i`; the classes are returned for the report (a class of two or
more members is ordered by Pass 1's seed order). An error means the recovery
failed (`NOSPEC`). -/
def recoveredOrder (addr? : IxName → Option Address) (inp : Input) :
    Except String (Array Nat × Array (Array IxName)) := do
  let specs ← recoverSpecs inp
  let members : Array _root_.Ix.Compile.Canon.CliqueMember := (inp.members.zip specs).map fun (d, v) =>
    { name := d.name, levelParams := d.levelParams, type := d.type, value := v }
  let addr' (n : IxName) : Option Address := (placeholderAddr? n).orElse fun _ => addr? n
  let (cls, _) ← _root_.Ix.Compile.Canon.cliqueClasses _root_.Ix.Compile.Canon.Rules.compiler addr'
    { kind := .noSpec, members }
  let order := cls.foldl (· ++ ·) #[]
  let some σ := members.mapM fun m => order.idxOf? m.name
    | throw "recovery: the classes do not order every member"
  unless isPerm σ do throw "recovery: the classes do not order every member"
  return (σ, cls)

end Tests.Ix.Compile.Clique.Common
