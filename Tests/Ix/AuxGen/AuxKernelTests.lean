module

public import LSpec
public import Ix.AuxGen.AuxKernel

/-!
Tests of the `AuxKernel` interface (`Ix.AuxGen.AuxKernel`, AuxGen M0):
- the interface answers exactly as the bridge it wraps (`TcScopeSt`), so
  switching the generators to it cannot move bytes;
- its refusals, one per reachable constructor;
- scopes as values (`staleScope`), including the hole a depth check alone
  leaves open;
- the fail-open answers are explicit `Option`s with named defaults;
- the elimination decision on small fixtures (Prop/Type, one constructor
  without fields, a result sort behind a reducible alias).

The rendering table of every `AuxKernelError` is in
`Tests.Ix.Compile.BridgeBoundaries`. Registered in `aux-gen-unit`.
-/

public section

namespace Tests.AuxGen.AuxKernel

open LSpec
open Ix.AuxGen
open Ix.CompileM (CompileM CompileEnv CompileError)
open Ix (Name Level Expr ConstantVal InductiveVal ConstructorVal ConstantInfo
  DefinitionVal)

private def nm (s : String) : Name := Name.mkStr .mkAnon s
private def prop : Expr := Expr.mkSort Level.mkZero
private def type0 : Expr := Expr.mkSort (Level.mkSucc Level.mkZero)
private def cnst (s : String) : Expr := Expr.mkConst (nm s) #[]

/-! ## Fixtures -/

private def inductive_ (n : String) (ty : Expr) (ctors : List (String × Expr))
    (numIndices : Nat := 0) : List (Name × ConstantInfo) :=
  let ind : ConstantInfo := .inductInfo
    { cnst := { name := nm n, levelParams := #[], type := ty }
      numParams := 0, numIndices, all := #[nm n]
      ctors := (ctors.map fun (c, _) => nm s!"{n}.{c}").toArray
      numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  let cs := ctors.zipIdx.map fun ((c, cty), i) =>
    (nm s!"{n}.{c}", ConstantInfo.ctorInfo
      { cnst := { name := nm s!"{n}.{c}", levelParams := #[], type := cty }
        induct := nm n, cidx := i, numParams := 0, numFields := 0, isUnsafe := false })
  (nm n, ind) :: cs

/-- `Set α := α → Prop` (reducible), two Prop inductives (`Two` with two
constructors, `One` with one constructor and no fields), a Type inductive
`T`, and an index family `S : Set Two` whose result sort sits behind the
alias. -/
private def consts : List (Name × ConstantInfo) :=
  let set : ConstantInfo := .defnInfo
    { cnst := { name := nm "Set", levelParams := #[]
                type := Expr.mkForallE (nm "α") type0 type0 .default }
      value := Expr.mkLam (nm "α") type0
        (Expr.mkForallE (nm "x") (Expr.mkBVar 0) prop .default) .default
      hints := .abbrev, safety := .safe, all := #[nm "Set"] }
  [(nm "Set", set)]
    ++ inductive_ "Two" prop [("a", cnst "Two"), ("b", cnst "Two")]
    ++ inductive_ "One" prop [("mk", cnst "One")]
    ++ inductive_ "T" type0 [("mk", cnst "T")]
    ++ inductive_ "S" (Expr.mkApp (cnst "Set") (cnst "Two"))
        [("mk", Expr.mkApp (cnst "S") (cnst "Two.a"))] (numIndices := 1)

private def fixture : CompileEnv := Id.run do
  let mut env : CompileEnv := default
  for (n, ci) in consts do
    env := { env with env := { env.env with consts := env.env.consts.insert n ci } }
  return env

private def maps : AddrMaps := { nameToAddr := fun _ => none }
private def kernel : AuxKernel := .tc maps

private def run (act : KBridgeM α) : Except CompileError α := do
  let ((value, _), _) ← CompileM.run fixture
    { all := {}, current := nm "test", mutCtx := default, univCtx := [] } {}
    (act.run AuxKernelCtx.new)
  return value

private def holds (act : KBridgeM Bool) : Bool := (run act).toOption == some true

private def refuses (act : KBridgeM α) (text : String) : Bool :=
  match run act with
  | .error (.unsupportedExpr msg) => (msg.splitOn text).length > 1
  | _ => false

private def decl (s : String) (ty : Expr) : LocalDecl :=
  { fvarName := nm s, binderName := nm s, domain := ty, info := .default }
private def α := decl "α" type0

private def find? (n : Name) : Option ConstantInfo :=
  (consts.find? (·.1 == n)).map (·.2)

private def original (n : String) : Option (InductiveVal × Array ConstructorVal) := do
  let .inductInfo ind ← find? (nm n) | none
  let ctors ← ind.ctors.mapM fun c => do
    let .ctorInfo ctor ← find? c | none
    pure ctor
  pure (ind, ctors)

/-! ## 1. The interface answers as the bridge -/

/-- The same queries, through the bridge's `TcScopeSt` and through
`AuxScope`, in two separate runs; the answers compare by `Expr`/`Level`
hash (bit parity). -/
private def interfaceIsBridge : Bool := Id.run do
  let u := nm "u"
  let setα := Expr.mkApp (cnst "Set") (Expr.mkFVar α.fvarName)
  let piα := Expr.mkForallE (nm "x") (Expr.mkFVar α.fvarName) prop .default
  let viaBridge : KBridgeM (Level × Level × Expr × Bool × Option Expr) := do
    ensureInKenvOf (nm "Set") maps
    let s ← TcScopeSt.new #[α] #[u] maps
    let l1 ← s.getLevel (Expr.mkSort (Level.mkParam u))
    let l2 ← s.getLevel (Expr.mkForallE (nm "y") (Expr.mkSort (Level.mkParam u)) type0 .default)
    let w ← s.whnfLean setα
    let d ← s.isDefEq setα piα
    let i ← s.inferLean (Expr.mkFVar α.fvarName)
    return (l1, l2, w, d, i)
  let viaInterface : KBridgeM (Level × Level × Expr × Bool × Option Expr) := do
    kernel.admitSource #[nm "Set"]
    let s ← AuxScope.new kernel #[α] #[u]
    let l1 ← s.getLevel (Expr.mkSort (Level.mkParam u))
    let l2 ← s.getLevel (Expr.mkForallE (nm "y") (Expr.mkSort (Level.mkParam u)) type0 .default)
    let w ← s.whnfOrInput setα
    let d ← s.isDefEqOrFalse setα piα
    let i ← s.inferType? (Expr.mkFVar α.fvarName)
    return (l1, l2, w, d, i)
  let (.ok b, .ok i) := (run viaBridge, run viaInterface) | return false
  -- and the answers are the expected ones
  return b == i && b.2.2.1 == piα && b.2.2.2.1 && b.2.2.2.2 == some type0

/-! ## 2. Refusals through the interface -/

private def unknownFVarRefusals : Bool :=
  let y := Expr.mkFVar (nm "y")
  let text := "toKexprStatic: unknown free variable y"
  refuses (do let s ← AuxScope.new kernel #[α] #[]; s.getLevel y) text
    && refuses (do let s ← AuxScope.new kernel #[α] #[]; s.whnf? y) text
    && refuses (do let s ← AuxScope.new kernel #[α] #[]; s.isDefEq? y y) text
    && refuses (do let s ← AuxScope.new kernel #[α] #[]; s.inferType? y) text

private def ingressRefusals : Bool :=
  refuses (do let s ← AuxScope.new kernel #[] #[]; s.getLevel (Expr.mkSort (Level.mkParam (nm "w"))))
      "unknown level param `w`"
    && refuses (do let s ← AuxScope.new kernel #[] #[]; s.getLevel (Expr.mkSort (Level.mkMvar (nm "m"))))
      "level metavariable"
    && refuses (do let s ← AuxScope.new kernel #[] #[]; s.inferType? (Expr.mkMVar (nm "m")))
      "toKexprStatic: expression metavariable"

private def scopeRefusals : Bool :=
  let x := decl "x" prop
  refuses (AuxScope.new kernel #[] #[nm "u", nm "u"]) "duplicate universe parameter 'u'"
    && refuses (AuxScope.new kernel #[x, x] #[]) "duplicate outer free variable 'x'"
    && refuses (do let s ← AuxScope.new kernel #[x] #[]; s.push #[x])
      "duplicate pushed free variable 'x'"
    && refuses (do let s ← AuxScope.new kernel #[x] #[]; s.pop #[x])
      "popLocals exceeds pushed local count"
    && refuses (do
        let s ← AuxScope.new kernel #[] #[]
        let s ← s.push #[x, decl "y" prop]
        s.pop #[x])
      "popLocals is not LIFO at 'x'"

private def kernelRefusals : Bool :=
  -- `Sort 0` applied to itself: inference fails, the level query refuses.
  refuses (do let s ← AuxScope.new kernel #[] #[]; s.getLevel (Expr.mkApp prop prop))
      "TcScope::get_level: tc.infer failed:"
    -- a block whose declared type is not a type: the decision refuses as
    -- `invalidMutualBlock`, never a fallback
    && (match run (kernel.elimDecision
          #[({ cnst := { name := nm "Bad", levelParams := #[], type := Expr.mkLit (.natVal 0) }
               numParams := 0, numIndices := 0, all := #[nm "Bad"], ctors := #[]
               numNested := 0, isRec := false, isUnsafe := false, isReflexive := false },
             #[])] 0) with
        | .error (.invalidMutualBlock msg) =>
          (msg.splitOn "compute_is_large_and_k:").length > 1 && (msg.splitOn "Bad").length > 1
        | _ => false)

/-! ## 3. Scopes as values -/

private def stale := "aux kernel: scope value superseded before"

/-- `s0 ← new; s1 ← s0.push [x]; s2 ← s1.pop [x]`: `s0` and `s2` denote the
live context and are served; `s1` is superseded. -/
private def pushPopValues : Bool :=
  let x := decl "x" (Expr.mkFVar α.fvarName)
  holds (do
      let s0 ← AuxScope.new kernel #[α] #[]
      let s1 ← s0.push #[x]
      let s2 ← s1.pop #[x]
      let a ← s0.inferType? (Expr.mkFVar α.fvarName)
      let b ← s2.inferType? (Expr.mkFVar α.fvarName)
      return a == some type0 && b == some type0 && s2.depth == 1 && s2.nOuter == 1)
    && refuses (do
      let s0 ← AuxScope.new kernel #[α] #[]
      let s1 ← s0.push #[x]
      discard <| s1.pop #[x]
      s1.inferType? (Expr.mkFVar x.fvarName)) stale

/-- `push [x]`, `pop`, `push [y]` (another type): the depth matches the old
`[x]` value, but its context is gone, so it is refused (depth alone would
answer `x` as `y`). -/
private def depthHole : Bool :=
  let x := decl "x" (Expr.mkFVar α.fvarName)
  let y := decl "y" prop
  refuses (do
    let s0 ← AuxScope.new kernel #[α] #[]
    let s1 ← s0.push #[x]
    let s2 ← s1.pop #[x]
    discard <| s2.push #[y]
    s1.inferType? (Expr.mkFVar x.fvarName)) stale

/-- A new scope, and the elimination decision, supersede every open one. -/
private def epochs : Bool :=
  refuses (do
      let s ← AuxScope.new kernel #[] #[]
      discard <| AuxScope.new kernel #[] #[]
      s.inferType? prop) stale
    && refuses (do
      let s ← AuxScope.new kernel #[] #[]
      let some two := original "Two" | return none
      discard <| kernel.elimDecision #[two] 0
      s.inferType? prop) stale

/-- A query whose kernel gives no answer leaves its scope live (`Ix.Tc`
restores its context on every outcome), and a caught refusal restores the
whole state, the epoch included. -/
private def failuresKeepScopes : Bool :=
  holds (do
      let s ← AuxScope.new kernel #[α] #[]
      -- `T.mk` is not admitted, so the kernel cannot type the application
      let r ← s.inferType? (Expr.mkApp (cnst "T.mk") prop)
      let after ← s.inferType? (Expr.mkFVar α.fvarName)
      return r.isNone && after == some type0)
    && holds (do
      let s ← AuxScope.new kernel #[α] #[]
      try
        discard <| AuxScope.new kernel #[] #[]
        throwBridge (.internal "test")
      catch _ => pure ()
      return (← s.inferType? (Expr.mkFVar α.fvarName)) == some type0)

/-! ## 4. The fail-open answers are explicit -/

/-- The generators' defaults are exactly `getD` of the explicit answers:
`whnfOrInput` is the input and `isDefEqOrFalse` is `false` when the kernel
gives no answer; and a kernel error is `none`, not a value (`inferType?` of
an application of a constant that was never admitted). -/
private def failOpenDefaults : Bool :=
  let stuck := Expr.mkApp (cnst "T.mk") prop
  let pairs : List (Expr × Expr) := [(stuck, prop), (stuck, stuck), (prop, prop), (type0, prop)]
  holds (do
    let s ← AuxScope.new kernel #[] #[]
    let mut ok := (← s.inferType? stuck).isNone
    for (a, b) in pairs do
      ok := ok && (← s.whnfOrInput a) == (← s.whnf? a).getD a
        && (← s.isDefEqOrFalse a b) == (← s.isDefEq? a b).getD false
    return ok)

/-! ## 6. The elimination decision -/

private def decision (n : String) : Option ElimDecision := do
  let o ← original n
  (run (kernel.elimDecision #[o] 0)).toOption

private def elimDecisions : Bool :=
  decision "Two" == some { isLarge := false, isProp := true }
    && decision "T" == some { isLarge := true, isProp := false }
    && decision "One" == some { isLarge := true, isProp := true }
    -- the result sort behind `Set Two`
    && decision "S" == some { isLarge := true, isProp := true }

def suite : List TestSeq := [
  test "AuxKernel: the interface answers exactly as the Ix.Tc bridge" interfaceIsBridge
  ++ test "AuxKernel: an unknown free variable is refused by every query" unknownFVarRefusals
  ++ test "AuxKernel: unknown level parameters and metavariables are refused" ingressRefusals
  ++ test "AuxKernel: scope discipline refusals" scopeRefusals
  ++ test "AuxKernel: kernel failures of fail-closed queries are refusals" kernelRefusals
  ++ test "AuxKernel: push/pop values; a superseded value is refused" pushPopValues
  ++ test "AuxKernel: a matching depth does not revive a gone context" depthHole
  ++ test "AuxKernel: a new scope or an elimination decision supersedes open scopes" epochs
  ++ test "AuxKernel: failed queries and caught refusals keep scopes live" failuresKeepScopes
  ++ test "AuxKernel: fail-open answers are explicit options with named defaults"
    failOpenDefaults
  ++ test "AuxKernel: elimination decisions (Prop, Type, K-like, behind an alias)" elimDecisions
]

end Tests.AuxGen.AuxKernel
