import LSpec
import Ix.AuxGen.Kernel

open LSpec Ix Ix.AuxGen Ix.CompileM

namespace Tests.Ix.Compile.BridgeBoundaries

private def nm (s : String) : Ix.Name := Ix.Name.fromLeanName s.toName
private def x := nm "x"
private def y := nm "y"
private def u := nm "u"
private def maps : AddrMaps := { nameToAddr := fun _ => none }

/-- The converter refused, and its rendered text (`AuxKernelError.render`,
the text the bridge emits) contains `part`. -/
private def failsWith (result : Except AuxKernelError α) (part : String) : Bool :=
  match result with
  | .ok _ => false
  | .error e => (e.render.splitOn part).length > 1

private def execute (act : KBridgeM α) : Except CompileError α := do
  let ((value, _), _) ← CompileM.run default
    { all := {}, current := x, mutCtx := default, univCtx := [] } {}
    (act.run AuxKernelCtx.new)
  pure value

private def bridgeFails (e : Expr) (part : String) : Bool :=
  match execute (leanExprToKexpr e #[] maps) with
  | .error (.unsupportedExpr message) => (message.splitOn part).length > 1
  | _ => false

/-- Bridge provisional IDs do not become addresses in the returned source
expression: its explicit source name survives and must be resolved anew by
the compiler. This is an executable boundary control, not a proof of the
whole compiler's no-escape property. -/
private def provisionalRoundtrip : Bool :=
  let source := Expr.mkConst x #[Level.mkParam u]
  match toKexprStatic source {} 0 #[u] maps with
  | .error _ => false
  | .ok kernel =>
    match kernel with
    | .const kid _ _ => kid.addr == x.getHash
      && (kexprToLean kernel 0 {} 0 #[u]).toOption == some source
    | _ => false

private def provisionalCompilation (resolved : Bool) : Bool := Id.run do
  let source := Expr.mkConst x #[]
  let .ok kernel := toKexprStatic source {} 0 #[] maps | return false
  let .ok restored := kexprToLean kernel 0 {} 0 #[] | return false
  let actual := Address.blake3 "compiled source content".toUTF8
  let env : CompileEnv := { (default : CompileEnv) with
    nameToAddr := if resolved then ({} : Std.HashMap _ _).insert x actual else {} }
  match CompileM.run env
      { all := {}, current := y, mutCtx := default, univCtx := [] } {}
      (compileExprNoSurgery restored) with
  | .ok (_, state) => return resolved && state.refs == #[actual]
  | .error (.missingConstant _) => return !resolved
  | .error _ => return false

/-- Distinct aliases sharing content retain their own names regardless of
the order in which the Meta intern table has seen them. -/
private def aliasHistory (reverse : Bool) : Bool :=
  let shared := Address.blake3 "same-content".toUTF8
  let aliasMaps : AddrMaps := { nameToAddr := fun _ => some shared }
  let action : KBridgeM Bool := do
    let inputs := if reverse then #[y, x] else #[x, y]
    for name in inputs do
      let source := Expr.mkConst name #[]
      let kernel ← leanExprToKexpr source #[] aliasMaps
      let result ← liftBridgeResult (kexprToLean kernel 0 {} 0 #[])
      unless result == source do return false
    return true
  (execute action).toOption == some true

private def whnfHistory (reverse : Bool) : Bool :=
  let shared := Address.blake3 "same-content".toUTF8
  let aliasMaps : AddrMaps := { nameToAddr := fun _ => some shared }
  let action : KBridgeM Bool := do
    for name in #[x, y] do
      kenvInsert ⟨shared, name⟩
        (.axio name #[] false 0 (Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero))
    let scope ← TcScopeSt.new #[] #[] aliasMaps
    let inputs := if reverse then #[y, x] else #[x, y]
    for name in inputs do
      let source := Expr.mkConst name #[]
      unless (← scope.whnfLean source) == source do return false
    return true
  (execute action).toOption == some true

private def constantUniverseBoundary : Bool :=
  let action : KBridgeM Bool := do
    let scope ← TcScopeSt.new #[] #[u] maps
    let parameter := Ix.Tc.KUniv.mkParam 0 u
    let level := Level.mkSucc Level.mkZero
    return failsWith (scope.kunivToLevelWithConstLevels parameter #[]) "out of range"
      && (scope.kunivToLevelWithConstLevels parameter #[level]).toOption == some level
  (execute action).toOption == some true


/-- Kernel metadata on every node survives egress, as in Rust
`kexpr_to_lean` (which re-wraps the node's `mdata` after every case). The
`let inner ← match` alternatives used `return`, which left the whole
function, so only `var`/`nat`/`str` kept their metadata. Here an `mdata`
layer sits on an application, on its head constant and on a λ, each with
two layers in a fixed order (outermost first). -/
private def mdataEverywhere : Bool :=
  let md (s : String) : Ix.Tc.MData := #[(nm "k", .ofString s)]
  let kx : MKExpr := Ix.Tc.KExpr.mkConst ⟨x.getHash, x⟩ #[] (mdata := #[md "c1", md "c2"])
  let ky : MKExpr := Ix.Tc.KExpr.mkConst ⟨y.getHash, y⟩ #[]
  let kapp := Ix.Tc.KExpr.mkApp kx ky (mdata := #[md "a1", md "a2"])
  let klam : MKExpr := Ix.Tc.KExpr.mkLam x Lean.BinderInfo.default (Ix.Tc.KExpr.mkSort Ix.Tc.KUniv.mkZero) kapp
    (mdata := #[md "l"])
  let wrap (ks : List String) (e : Expr) : Expr :=
    ks.foldr (fun s acc => Expr.mkMData (md s) acc) e
  let lx := wrap ["c1", "c2"] (Expr.mkConst x #[])
  let lapp := wrap ["a1", "a2"] (Expr.mkApp lx (Expr.mkConst y #[]))
  let llam := wrap ["l"] (Expr.mkLam x (Expr.mkSort Level.mkZero) lapp .default)
  (kexprToLean kapp 0 {} 0 #[]).toOption == some lapp
    && (kexprToLean klam 0 {} 0 #[]).toOption == some llam
    -- valid neighbour: no metadata gives the bare term
    && (kexprToLean (Ix.Tc.KExpr.mkApp (Ix.Tc.KExpr.mkConst ⟨x.getHash, x⟩ #[]) ky) 0 {} 0 #[]).toOption
      == some (Expr.mkApp (Expr.mkConst x #[]) (Expr.mkConst y #[]))
/-- Bound-variable and projection indices beyond `u64` are refused by both
ingresses (they used to wrap through `UInt64.ofNat`; Rust panicked), with the
kernel crate's wording; `2⁶⁴ - 1` is the valid neighbour. -/
private def wideIndices : Bool :=
  let big := 2 ^ 64
  let subject := Expr.mkLit (.natVal 0)
  let openBVar := failsWith (toKexprStatic (Expr.mkBVar big) {} 0 #[] maps)
    "toKexprStatic: bound variable index 18446744073709551616 exceeds u64"
  let openProj := failsWith (toKexprStatic (Expr.mkProj x big subject) {} 0 #[] maps)
    "toKexprStatic: projection index 18446744073709551616 of x exceeds u64"
  let openValid :=
    (match toKexprStatic (Expr.mkBVar (big - 1)) {} 0 #[] maps with
      | .ok (.var idx _ _) => idx == UInt64.ofNat (big - 1)
      | _ => false) &&
    (match toKexprStatic (Expr.mkProj x (big - 1) subject) {} 0 #[] maps with
      | .ok (.prj _ field _ _) => field == UInt64.ofNat (big - 1)
      | _ => false)
  let closedBVar := bridgeFails (Expr.mkBVar big)
    "bound variable index 18446744073709551616 exceeds u64 in closed ingress"
  let closedProj := bridgeFails (Expr.mkProj x big subject)
    "projection index 18446744073709551616 of x exceeds u64 in closed ingress"
  let closedValid := match execute (leanExprToKexpr (Expr.mkBVar (big - 1)) #[] maps) with
    | .ok (.var idx _ _) => idx == UInt64.ofNat (big - 1)
    | _ => false
  openBVar && openProj && openValid && closedBVar && closedProj && closedValid

/-- A Nat literal of `2⁶⁴` or more is addressed by its full little-endian
bytes (`Ix.Tc`'s `natBlob`) in both ingresses, never by a truncation; below
`2⁶⁴` the address stays the u64's eight bytes. -/
private def largeNatLiterals : Bool :=
  let blobOf {ε : Type} (r : Except ε MKExpr) : Option Address := match r with
    | .ok (.nat _ blob _) => some blob
    | _ => none
  let both (n : Nat) : Option Address × Option Address :=
    (blobOf (toKexprStatic (Expr.mkLit (.natVal n)) {} 0 #[] maps),
     blobOf (execute (leanExprToKexpr (Expr.mkLit (.natVal n)) #[] maps)))
  let big := 2 ^ 64
  let bigBlob := some (Address.blake3 ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 1]⟩)
  let maxBlob := some (Address.blake3 (UInt64.ofNat (big - 1)).toLEBytes)
  let oneBlob := some (Address.blake3 (1 : UInt64).toLEBytes)
  both big == (bigBlob, bigBlob)
    && bigBlob == some (Ix.Tc.KExpr.natBlob big)
    && both (big - 1) == (maxBlob, maxBlob)
    && both 1 == (oneBlob, oneBlob)
    -- the truncation the bridge must not produce
    && bigBlob != some (Address.blake3 (UInt64.ofNat big).toLEBytes)

/-- Every refusal renders to the text CQ2.7 landed (prefix included) and
becomes the compiler error it threw before the type existed: the
elimination decision's kernel failures `invalidMutualBlock`, the rest
`unsupportedExpr`. The `Ix.Tc` texts embedded in `kernel` details (aux-cert
WB-A3's `function expected, got Sort u`) pass through unchanged. -/
private def renderingTable : Bool :=
  let a := Address.blake3 "render".toUTF8
  let rows : List (AuxKernelError × String) := [
    (.unknownLevelParam u #[x, y],
      "aux kernel bridge: unknown level param `u` not found in param_names [x, y]"),
    (.levelMVar, "aux kernel bridge: leanLevelToKuniv: level metavariable"),
    (.closedFVar x, "aux kernel bridge: free variable x in closed ingress"),
    (.closedMVar, "aux kernel bridge: expression metavariable in closed ingress"),
    (.outerMData, "aux kernel bridge: metadata stripping left an outer metadata layer"),
    (.closedBVarIndex 7, "aux kernel bridge: bound variable index 7 exceeds u64 in closed ingress"),
    (.closedProjIndex x 7,
      "aux kernel bridge: projection index 7 of x exceeds u64 in closed ingress"),
    (.unknownFVar x, "aux kernel bridge: toKexprStatic: unknown free variable x"),
    (.fvarOutsideDepth x 2,
      "aux kernel bridge: toKexprStatic: free variable x outside context depth 2"),
    (.openMVar, "aux kernel bridge: toKexprStatic: expression metavariable"),
    (.openBVarIndex 7, "aux kernel bridge: toKexprStatic: bound variable index 7 exceeds u64"),
    (.openProjIndex x 7,
      "aux kernel bridge: toKexprStatic: projection index 7 of x exceeds u64"),
    (.varOutOfRange, "aux kernel bridge: kexprToLean: Var index out of range of outer context"),
    (.missingFVarAt 3, "aux kernel bridge: kexprToLean: missing free variable at outer level 3"),
    (.duplicateFVarAt 3,
      "aux kernel bridge: kexprToLean: duplicate free variable identities at outer level 3"),
    (.leakedKernelFVar 4, "aux kernel bridge: kexprToLean: leaked kernel free variable 4"),
    (.levelParamIndex 1, "aux kernel bridge: kunivToLevel: universe parameter index 1 out of range"),
    (.constLevelArgIndex 1, "aux kernel bridge: kunivToLevelWithConstLevels: constant universe \
argument index 1 out of range"),
    (.duplicateLevelParam u, "aux kernel bridge: duplicate universe parameter 'u'"),
    (.duplicateOuterFVar x, "aux kernel bridge: duplicate outer free variable 'x'"),
    (.duplicatePushedFVar x, "aux kernel bridge: duplicate pushed free variable 'x'"),
    (.staleDepth "pushLocals", "aux kernel bridge: stale scope depth before pushLocals"),
    (.staleScope "push", "aux kernel: scope value superseded before push"),
    (.popExceedsPushed, "aux kernel bridge: popLocals exceeds pushed local count"),
    (.popNotLifo x, "aux kernel bridge: popLocals is not LIFO at 'x'"),
    (.noProvenance a, s!"bridge fault: no forward source provenance for {a}"),
    (.provenanceChanged x, "bridge fault: source address changed for x"),
    (.kernel (.inferUnknownConst a) "",
      s!"TcScope::get_level: tc.infer failed: unknown constant {(toString a).take 12}"),
    (.kernel .infer "function expected, got Sort u",
      "TcScope::get_level: tc.infer failed: function expected, got Sort u"),
    (.kernel .ensureSort "e", "TcScope::get_level: ensure_sort failed: e"),
    (.internal "inference retry exited without a result",
      "aux kernel bridge: inference retry exited without a result")]
  let decisions : List (AuxKernelError × String) := [
    (.kernel (.resultSort "T") "e", "compute_is_large_and_k: TC failed for T: e"),
    (.kernel (.largeElim "T") "e", "compute_is_large_and_k: is_large_eliminator failed for T: e")]
  rows.all (fun (e, text) => e.render == text && e.toCompileError == .unsupportedExpr text)
    && decisions.all fun (e, text) =>
      e.render == text && e.toCompileError == .invalidMutualBlock text

def suite : List TestSeq := [
  test "every refusal renders to the bridge's landed text and compiler error" renderingTable
  ++ test "bound-variable and projection indices beyond u64 are refused" wideIndices
  ++ test "Nat literals beyond u64 are addressed by their full bytes" largeNatLiterals
  ++ test "unknown universe parameters are explicit errors"
    (failsWith (leanLevelToKuniv (Level.mkParam u) #[]) "unknown level param")
  ++ test "universe metavariables are explicit errors"
    (failsWith (leanLevelToKuniv (Level.mkMvar u) #[]) "level metavariable")
  ++ test "egress refuses missing positional universe parameters"
    (failsWith (kunivToLevel (Ix.Tc.KUniv.mkParam 1 u) #[u]) "out of range")
  ++ test "constant egress refuses missing positional universe arguments"
    (failsWith (kexprToLean (Ix.Tc.KExpr.mkConst ⟨x.getHash, x⟩
      #[Ix.Tc.KUniv.mkParam 1 u]) 0 {} 0 #[u]) "out of range")
  ++ test "constant universe substitution never borrows an ambient parameter"
    constantUniverseBoundary
  ++ test "closed ingress rejects free variables" (bridgeFails (Expr.mkFVar x) "free variable")
  ++ test "closed ingress rejects expression metavariables" (bridgeFails (Expr.mkMVar x) "metavariable")
  ++ test "closed ingress reports unknown universe parameters"
    (bridgeFails (Expr.mkSort (Level.mkParam u)) "unknown level param")
  ++ test "open ingress rejects missing context variables"
    (failsWith (toKexprStatic (Expr.mkFVar x) {} 1 #[] maps) "unknown free variable")
  ++ test "open ingress rejects a level beyond the context"
    (failsWith (toKexprStatic (Expr.mkFVar x) (({} : Std.HashMap _ _).insert x 1) 1 #[] maps)
      "outside context depth")
  ++ test "egress rejects out-of-range outer variables"
    (failsWith (kexprToLean (Ix.Tc.KExpr.mkVar 1 x) 1 {} 0 #[]) "out of range")
  ++ test "egress rejects a missing context identity"
    (failsWith (kexprToLean (Ix.Tc.KExpr.mkVar 0 x) 1 {} 0 #[]) "missing free variable")
  ++ test "egress rejects duplicate context levels in both insertion orders"
    ([[(x, 0), (y, 0)], [(y, 0), (x, 0)]].all fun entries =>
      failsWith (kexprToLean (Ix.Tc.KExpr.mkVar 0 x) 1
        (Std.HashMap.ofList entries) 0 #[]) "duplicate free variable")
  ++ test "valid outer free variable roundtrips"
    (((do
      let context := ({} : Std.HashMap Ix.Name Nat).insert x 0
      let kernel ← toKexprStatic (Expr.mkFVar x) context 1 #[] maps
      kexprToLean kernel 1 context 0 #[]).toOption) == some (Expr.mkFVar x))
  ++ test "provisional identifiers egress through source names" provisionalRoundtrip
  ++ test "egressed provisional IDs compile through the actual source address" (provisionalCompilation true)
  ++ test "unresolved egressed IDs are refused instead of emitted" (provisionalCompilation false)
  ++ test "alias ingress order preserves source names" (aliasHistory false && aliasHistory true)
  ++ test "egress re-wraps kernel metadata on every node"
    mdataEverywhere
  ++ test "semantic WHNF cache history preserves the requested source alias"
    (whnfHistory false && whnfHistory true)
]

end Tests.Ix.Compile.BridgeBoundaries
